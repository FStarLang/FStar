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
                                               Some
                                                 (Prims.strcat "kinding_"
                                                    tsym)
                                                in
                                             let uu____2689 =
                                               let uu____2694 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____2694, a_name, a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2689
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
                                               Some
                                                 (Prims.strcat "pre_typing_"
                                                    tsym)
                                                in
                                             let uu____2709 =
                                               let uu____2714 =
                                                 let uu____2715 =
                                                   let uu____2721 =
                                                     let uu____2722 =
                                                       let uu____2725 =
                                                         let uu____2726 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2726
                                                          in
                                                       (f_has_t, uu____2725)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2722
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2721)
                                                    in
                                                 mkForall_fuel uu____2715  in
                                               (uu____2714,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2709
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Some
                                                 (Prims.strcat
                                                    "interpretation_" tsym)
                                                in
                                             let uu____2741 =
                                               let uu____2746 =
                                                 let uu____2747 =
                                                   let uu____2753 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2753)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2747
                                                  in
                                               (uu____2746, a_name, a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2741
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
                       Some (Prims.strcat "non_total_function_typing_" tsym)
                        in
                     let uu____2786 =
                       let uu____2791 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____2791, (Some "Typing for non-total arrows"),
                         a_name)
                        in
                     FStar_SMTEncoding_Term.Assume uu____2786  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Some (Prims.strcat "pre_typing_" tsym)  in
                     let uu____2802 =
                       let uu____2807 =
                         let uu____2808 =
                           let uu____2814 =
                             let uu____2815 =
                               let uu____2818 =
                                 let uu____2819 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2819
                                  in
                               (f_has_t, uu____2818)  in
                             FStar_SMTEncoding_Util.mkImp uu____2815  in
                           ([[f_has_t]], [fsym], uu____2814)  in
                         mkForall_fuel uu____2808  in
                       (uu____2807, a_name, a_name)  in
                     FStar_SMTEncoding_Term.Assume uu____2802  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2834 ->
           let uu____2839 =
             let uu____2842 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2842 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2847;
                 FStar_Syntax_Syntax.pos = uu____2848;
                 FStar_Syntax_Syntax.vars = uu____2849;_} ->
                 let uu____2856 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2856 with
                  | (b,f1) ->
                      let uu____2870 =
                        let uu____2871 = FStar_List.hd b  in
                        Prims.fst uu____2871  in
                      (uu____2870, f1))
             | uu____2876 -> failwith "impossible"  in
           (match uu____2839 with
            | (x,f) ->
                let uu____2883 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2883 with
                 | (base_t,decls) ->
                     let uu____2890 = gen_term_var env x  in
                     (match uu____2890 with
                      | (x1,xtm,env') ->
                          let uu____2899 = encode_formula f env'  in
                          (match uu____2899 with
                           | (refinement,decls') ->
                               let uu____2906 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2906 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2914 =
                                        let uu____2917 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t
                                           in
                                        (uu____2917, refinement)  in
                                      FStar_SMTEncoding_Util.mkAnd uu____2914
                                       in
                                    let cvars =
                                      let uu____2922 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right uu____2922
                                        (FStar_List.filter
                                           (fun uu____2928  ->
                                              match uu____2928 with
                                              | (y,uu____2932) ->
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
                                    let uu____2951 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2951 with
                                     | Some (t1,uu____2966,uu____2967) ->
                                         let uu____2977 =
                                           let uu____2978 =
                                             let uu____2982 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (t1, uu____2982)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2978
                                            in
                                         (uu____2977, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2998 =
                                             let uu____2999 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash
                                                in
                                             Prims.strcat "Tm_refine_"
                                               uu____2999
                                              in
                                           varops.mk_unique uu____2998  in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars  in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____3008 =
                                             let uu____3012 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars
                                                in
                                             (tsym, uu____3012)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3008
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
                                           let uu____3022 =
                                             let uu____3027 =
                                               let uu____3028 =
                                                 let uu____3034 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3034)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3028
                                                in
                                             (uu____3027,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Some
                                                  (Prims.strcat "haseq" tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3022
                                            in
                                         let t_kinding =
                                           let uu____3045 =
                                             let uu____3050 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind)
                                                in
                                             (uu____3050,
                                               (Some "refinement kinding"),
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_kinding_"
                                                     tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3045
                                            in
                                         let t_interp =
                                           let uu____3061 =
                                             let uu____3066 =
                                               let uu____3067 =
                                                 let uu____3073 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3073)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3067
                                                in
                                             let uu____3085 =
                                               let uu____3087 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3087  in
                                             (uu____3066, uu____3085,
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_interpretation_"
                                                     tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3061
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
             let uu____3116 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3116  in
           let uu____3120 = encode_term_pred None k env ttm  in
           (match uu____3120 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3128 =
                    let uu____3133 =
                      let uu____3135 =
                        let uu____3136 =
                          let uu____3137 =
                            let uu____3138 = FStar_Unionfind.uvar_id uv  in
                            FStar_All.pipe_left FStar_Util.string_of_int
                              uu____3138
                             in
                          FStar_Util.format1 "uvar_typing_%s" uu____3137  in
                        varops.mk_unique uu____3136  in
                      Some uu____3135  in
                    (t_has_k, (Some "Uvar typing"), uu____3133)  in
                  FStar_SMTEncoding_Term.Assume uu____3128  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3145 ->
           let uu____3155 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3155 with
            | (head1,args_e) ->
                let uu____3183 =
                  let uu____3191 =
                    let uu____3192 = FStar_Syntax_Subst.compress head1  in
                    uu____3192.FStar_Syntax_Syntax.n  in
                  (uu____3191, args_e)  in
                (match uu____3183 with
                 | (uu____3202,uu____3203) when head_redex env head1 ->
                     let uu____3214 = whnf env t  in
                     encode_term uu____3214 env
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
                     let uu____3288 = encode_term v1 env  in
                     (match uu____3288 with
                      | (v11,decls1) ->
                          let uu____3295 = encode_term v2 env  in
                          (match uu____3295 with
                           | (v21,decls2) ->
                               let uu____3302 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3302,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3304) ->
                     let e0 =
                       let uu____3318 =
                         let uu____3321 =
                           let uu____3322 =
                             let uu____3332 =
                               let uu____3338 = FStar_List.hd args_e  in
                               [uu____3338]  in
                             (head1, uu____3332)  in
                           FStar_Syntax_Syntax.Tm_app uu____3322  in
                         FStar_Syntax_Syntax.mk uu____3321  in
                       uu____3318 None head1.FStar_Syntax_Syntax.pos  in
                     ((let uu____3371 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____3371
                       then
                         let uu____3372 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3372
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
                       (let uu____3376 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        if uu____3376
                        then
                          let uu____3377 =
                            FStar_Syntax_Print.term_to_string e01  in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3377
                        else ());
                       (let e02 =
                          let uu____3380 =
                            let uu____3381 =
                              let uu____3382 =
                                FStar_Syntax_Subst.compress e01  in
                              uu____3382.FStar_Syntax_Syntax.n  in
                            match uu____3381 with
                            | FStar_Syntax_Syntax.Tm_app uu____3385 -> false
                            | uu____3395 -> true  in
                          if uu____3380
                          then e01
                          else
                            (let uu____3397 =
                               FStar_Syntax_Util.head_and_args e01  in
                             match uu____3397 with
                             | (head2,args) ->
                                 let uu____3423 =
                                   let uu____3424 =
                                     let uu____3425 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____3425.FStar_Syntax_Syntax.n  in
                                   match uu____3424 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3428 -> false  in
                                 if uu____3423
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3444 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01)
                           in
                        let e =
                          match args_e with
                          | uu____3452::[] -> e02
                          | uu____3465 ->
                              let uu____3471 =
                                let uu____3474 =
                                  let uu____3475 =
                                    let uu____3485 = FStar_List.tl args_e  in
                                    (e02, uu____3485)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3475  in
                                FStar_Syntax_Syntax.mk uu____3474  in
                              uu____3471 None t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3508),(arg,uu____3510)::[]) -> encode_term arg env
                 | uu____3528 ->
                     let uu____3536 = encode_args args_e env  in
                     (match uu____3536 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3569 = encode_term head1 env  in
                            match uu____3569 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3608 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3608 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3650  ->
                                                 fun uu____3651  ->
                                                   match (uu____3650,
                                                           uu____3651)
                                                   with
                                                   | ((bv,uu____3665),
                                                      (a,uu____3667)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3681 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3681
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3686 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3686 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3696 =
                                                   let uu____3701 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3706 =
                                                     let uu____3708 =
                                                       let uu____3709 =
                                                         let uu____3710 =
                                                           let uu____3711 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm
                                                              in
                                                           FStar_Util.digest_of_string
                                                             uu____3711
                                                            in
                                                         Prims.strcat
                                                           "partial_app_typing_"
                                                           uu____3710
                                                          in
                                                       varops.mk_unique
                                                         uu____3709
                                                        in
                                                     Some uu____3708  in
                                                   (uu____3701,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3706)
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3696
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3729 = lookup_free_var_sym env fv  in
                            match uu____3729 with
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
                                let uu____3767 =
                                  let uu____3768 =
                                    let uu____3771 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____3771 Prims.fst
                                     in
                                  FStar_All.pipe_right uu____3768 Prims.snd
                                   in
                                Some uu____3767
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3790,(FStar_Util.Inl t1,uu____3792),uu____3793)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3831,(FStar_Util.Inr c,uu____3833),uu____3834)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3872 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3892 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3892
                                  in
                               let uu____3893 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____3893 with
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
                                     | uu____3918 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3963 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3963 with
            | (bs1,body1,opening) ->
                let fallback uu____3978 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____3983 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____3983, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3994 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1  in
                      Prims.op_Negation uu____3994
                  | FStar_Util.Inr (eff,uu____3996) ->
                      let uu____4002 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____4002 Prims.op_Negation
                   in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2  in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4047 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4048 = env1.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4048.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4048.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4048.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4048.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4048.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4048.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4048.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4048.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4048.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4048.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4048.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4048.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4048.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4048.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4048.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4048.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4048.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4048.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4048.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4048.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4048.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4048.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4048.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4047 FStar_Syntax_Syntax.U_unknown
                           in
                        let uu____4049 =
                          let uu____4050 = FStar_Syntax_Syntax.mk_Total typ
                             in
                          FStar_Syntax_Util.lcomp_of_comp uu____4050  in
                        FStar_Util.Inl uu____4049
                    | FStar_Util.Inr (eff_name,uu____4057) -> c  in
                  (c1, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4088 =
                        let uu____4089 = lc1.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____4089  in
                      FStar_All.pipe_right uu____4088
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4101 =
                        let uu____4102 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____4102 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4110 =
                          let uu____4111 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____4111  in
                        FStar_All.pipe_right uu____4110
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4115 =
                             let uu____4116 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____4116  in
                           FStar_All.pipe_right uu____4115
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____4127 =
                         let uu____4128 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4128
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4127);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc  in
                     let uu____4143 =
                       (is_impure lc1) &&
                         (let uu____4144 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1
                             in
                          Prims.op_Negation uu____4144)
                        in
                     if uu____4143
                     then fallback ()
                     else
                       (let uu____4148 = encode_binders None bs1 env  in
                        match uu____4148 with
                        | (vars,guards,envbody,decls,uu____4163) ->
                            let uu____4170 =
                              let uu____4178 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1
                                 in
                              if uu____4178
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1)  in
                            (match uu____4170 with
                             | (lc2,body2) ->
                                 let uu____4203 = encode_term body2 envbody
                                    in
                                 (match uu____4203 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4211 =
                                          let uu____4217 =
                                            let uu____4218 =
                                              let uu____4221 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____4221, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4218
                                             in
                                          ([], vars, uu____4217)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4211
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
                                      let uu____4232 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____4232 with
                                       | Some (t1,uu____4247,uu____4248) ->
                                           let uu____4258 =
                                             let uu____4259 =
                                               let uu____4263 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (t1, uu____4263)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4259
                                              in
                                           (uu____4258, [])
                                       | None  ->
                                           let uu____4274 =
                                             is_eta env vars body3  in
                                           (match uu____4274 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars
                                                   in
                                                let fsym =
                                                  let uu____4285 =
                                                    let uu____4286 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash
                                                       in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4286
                                                     in
                                                  varops.mk_unique uu____4285
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  let uu____4291 =
                                                    let uu____4295 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars
                                                       in
                                                    (fsym, uu____4295)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4291
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  let uu____4303 =
                                                    codomain_eff lc2  in
                                                  match uu____4303 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c
                                                         in
                                                      let uu____4310 =
                                                        encode_term_pred None
                                                          tfun env f
                                                         in
                                                      (match uu____4310 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Some
                                                               (Prims.strcat
                                                                  "typing_"
                                                                  fsym)
                                                              in
                                                           let uu____4318 =
                                                             let uu____4320 =
                                                               let uu____4321
                                                                 =
                                                                 let uu____4326
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                    in
                                                                 (uu____4326,
                                                                   a_name,
                                                                   a_name)
                                                                  in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4321
                                                                in
                                                             [uu____4320]  in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4318)
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Some
                                                      (Prims.strcat
                                                         "interpretation_"
                                                         fsym)
                                                     in
                                                  let uu____4336 =
                                                    let uu____4341 =
                                                      let uu____4342 =
                                                        let uu____4348 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4348)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4342
                                                       in
                                                    (uu____4341, a_name,
                                                      a_name)
                                                     in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4336
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
           ((uu____4367,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4368;
                          FStar_Syntax_Syntax.lbunivs = uu____4369;
                          FStar_Syntax_Syntax.lbtyp = uu____4370;
                          FStar_Syntax_Syntax.lbeff = uu____4371;
                          FStar_Syntax_Syntax.lbdef = uu____4372;_}::uu____4373),uu____4374)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4392;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4394;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4410 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4423 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4423, [decl_e])))
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
              let uu____4465 = encode_term e1 env  in
              match uu____4465 with
              | (ee1,decls1) ->
                  let uu____4472 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4472 with
                   | (xs,e21) ->
                       let uu____4486 = FStar_List.hd xs  in
                       (match uu____4486 with
                        | (x1,uu____4494) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4496 = encode_body e21 env'  in
                            (match uu____4496 with
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
            let uu____4518 =
              let uu____4522 =
                let uu____4523 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4523  in
              gen_term_var env uu____4522  in
            match uu____4518 with
            | (scrsym,scr',env1) ->
                let uu____4537 = encode_term e env1  in
                (match uu____4537 with
                 | (scr,decls) ->
                     let uu____4544 =
                       let encode_branch b uu____4560 =
                         match uu____4560 with
                         | (else_case,decls1) ->
                             let uu____4571 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4571 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p  in
                                  FStar_List.fold_right
                                    (fun uu____4601  ->
                                       fun uu____4602  ->
                                         match (uu____4601, uu____4602) with
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
                                                       fun uu____4639  ->
                                                         match uu____4639
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1)
                                                in
                                             let uu____4644 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4659 =
                                                     encode_term w1 env2  in
                                                   (match uu____4659 with
                                                    | (w2,decls21) ->
                                                        let uu____4667 =
                                                          let uu____4668 =
                                                            let uu____4671 =
                                                              let uu____4672
                                                                =
                                                                let uu____4675
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4675)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4672
                                                               in
                                                            (guard,
                                                              uu____4671)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4668
                                                           in
                                                        (uu____4667, decls21))
                                                in
                                             (match uu____4644 with
                                              | (guard1,decls21) ->
                                                  let uu____4683 =
                                                    encode_br br env2  in
                                                  (match uu____4683 with
                                                   | (br1,decls3) ->
                                                       let uu____4691 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4691,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4544 with
                      | (match_tm,decls1) ->
                          let uu____4703 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4703, decls1)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4734 ->
          let uu____4735 = encode_one_pat env pat  in [uu____4735]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4747 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4747
       then
         let uu____4748 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4748
       else ());
      (let uu____4750 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4750 with
       | (vars,pat_term) ->
           let uu____4760 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4783  ->
                     fun v1  ->
                       match uu____4783 with
                       | (env1,vars1) ->
                           let uu____4811 = gen_term_var env1 v1  in
                           (match uu____4811 with
                            | (xx,uu____4823,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4760 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4870 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4878 =
                        let uu____4881 = encode_const c  in
                        (scrutinee, uu____4881)  in
                      FStar_SMTEncoding_Util.mkEq uu____4878
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4900 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____4900 with
                        | (uu____4904,uu____4905::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4907 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4928  ->
                                  match uu____4928 with
                                  | (arg,uu____4934) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4944 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4944))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4963 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4978 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4993 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5015  ->
                                  match uu____5015 with
                                  | (arg,uu____5024) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5034 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____5034))
                         in
                      FStar_All.pipe_right uu____4993 FStar_List.flatten
                   in
                let pat_term1 uu____5050 = encode_term pat_term env1  in
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
      let uu____5057 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5072  ->
                fun uu____5073  ->
                  match (uu____5072, uu____5073) with
                  | ((tms,decls),(t,uu____5093)) ->
                      let uu____5104 = encode_term t env  in
                      (match uu____5104 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5057 with | (l1,decls) -> ((FStar_List.rev l1), decls)

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
            let uu____5142 = FStar_Syntax_Util.list_elements e  in
            match uu____5142 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____5160 =
              let uu____5170 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____5170 FStar_Syntax_Util.head_and_args
               in
            match uu____5160 with
            | (head1,args) ->
                let uu____5201 =
                  let uu____5209 =
                    let uu____5210 = FStar_Syntax_Util.un_uinst head1  in
                    uu____5210.FStar_Syntax_Syntax.n  in
                  (uu____5209, args)  in
                (match uu____5201 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5224,uu____5225)::(e,uu____5227)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5258)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5279 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____5312 =
                let uu____5322 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____5322
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____5312 with
              | (head1,args) ->
                  let uu____5351 =
                    let uu____5359 =
                      let uu____5360 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5360.FStar_Syntax_Syntax.n  in
                    (uu____5359, args)  in
                  (match uu____5351 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5373)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5393 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5411 = smt_pat_or t1  in
                (match uu____5411 with
                 | Some e ->
                     let uu____5427 = list_elements1 e  in
                     FStar_All.pipe_right uu____5427
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5444 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5444
                               (FStar_List.map one_pat)))
                 | uu____5458 ->
                     let uu____5462 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5462])
            | uu____5493 ->
                let uu____5495 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5495]
             in
          let uu____5526 =
            let uu____5542 =
              let uu____5543 = FStar_Syntax_Subst.compress t  in
              uu____5543.FStar_Syntax_Syntax.n  in
            match uu____5542 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5573 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5573 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5608;
                            FStar_Syntax_Syntax.effect_name = uu____5609;
                            FStar_Syntax_Syntax.result_typ = uu____5610;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5612)::(post,uu____5614)::(pats,uu____5616)::[];
                            FStar_Syntax_Syntax.flags = uu____5617;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5651 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5651)
                      | uu____5670 -> failwith "impos"))
            | uu____5686 -> failwith "Impos"  in
          match uu____5526 with
          | (binders,pre,post,patterns) ->
              let uu____5730 = encode_binders None binders env  in
              (match uu____5730 with
               | (vars,guards,env1,decls,uu____5745) ->
                   let uu____5752 =
                     let uu____5759 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5790 =
                                 let uu____5795 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5811  ->
                                           match uu____5811 with
                                           | (t1,uu____5818) ->
                                               encode_term t1
                                                 (let uu___146_5821 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___146_5821.bindings);
                                                    depth =
                                                      (uu___146_5821.depth);
                                                    tcenv =
                                                      (uu___146_5821.tcenv);
                                                    warn =
                                                      (uu___146_5821.warn);
                                                    cache =
                                                      (uu___146_5821.cache);
                                                    nolabels =
                                                      (uu___146_5821.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5821.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5795
                                   FStar_List.unzip
                                  in
                               match uu____5790 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5759 FStar_List.unzip  in
                   (match uu____5752 with
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
                                           let uu____5885 =
                                             let uu____5886 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5886 e
                                              in
                                           uu____5885 :: p))
                               | uu____5887 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5916 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5916 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5924 =
                                           let uu____5925 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5925 tl1
                                            in
                                         aux uu____5924 vars2
                                     | uu____5926 -> pats  in
                                   let uu____5930 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5930 vars)
                           in
                        let env2 =
                          let uu___147_5932 = env1  in
                          {
                            bindings = (uu___147_5932.bindings);
                            depth = (uu___147_5932.depth);
                            tcenv = (uu___147_5932.tcenv);
                            warn = (uu___147_5932.warn);
                            cache = (uu___147_5932.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5932.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5932.encode_non_total_function_typ)
                          }  in
                        let uu____5933 =
                          let uu____5936 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5936 env2  in
                        (match uu____5933 with
                         | (pre1,decls'') ->
                             let uu____5941 =
                               let uu____5944 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5944 env2  in
                             (match uu____5941 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5951 =
                                    let uu____5952 =
                                      let uu____5958 =
                                        let uu____5959 =
                                          let uu____5962 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5962, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5959
                                         in
                                      (pats1, vars, uu____5958)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5952
                                     in
                                  (uu____5951, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5975 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5975
        then
          let uu____5976 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5977 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5976 uu____5977
        else ()  in
      let enc f r l =
        let uu____6004 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6017 = encode_term (Prims.fst x) env  in
                 match uu____6017 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____6004 with
        | (decls,args) ->
            let uu____6034 =
              let uu___148_6035 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6035.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6035.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6034, decls)
         in
      let const_op f r uu____6054 = let uu____6057 = f r  in (uu____6057, [])
         in
      let un_op f l =
        let uu____6073 = FStar_List.hd l  in FStar_All.pipe_left f uu____6073
         in
      let bin_op f uu___120_6086 =
        match uu___120_6086 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6094 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6121 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6130  ->
                 match uu____6130 with
                 | (t,uu____6138) ->
                     let uu____6139 = encode_formula t env  in
                     (match uu____6139 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6121 with
        | (decls,phis) ->
            let uu____6156 =
              let uu___149_6157 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6157.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6157.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6156, decls)
         in
      let eq_op r uu___121_6173 =
        match uu___121_6173 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6233 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6233 r [e1; e2]
        | l ->
            let uu____6253 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6253 r l
         in
      let mk_imp1 r uu___122_6272 =
        match uu___122_6272 with
        | (lhs,uu____6276)::(rhs,uu____6278)::[] ->
            let uu____6299 = encode_formula rhs env  in
            (match uu____6299 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6308) ->
                      (l1, decls1)
                  | uu____6311 ->
                      let uu____6312 = encode_formula lhs env  in
                      (match uu____6312 with
                       | (l2,decls2) ->
                           let uu____6319 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6319, (FStar_List.append decls1 decls2)))))
        | uu____6321 -> failwith "impossible"  in
      let mk_ite r uu___123_6336 =
        match uu___123_6336 with
        | (guard,uu____6340)::(_then,uu____6342)::(_else,uu____6344)::[] ->
            let uu____6373 = encode_formula guard env  in
            (match uu____6373 with
             | (g,decls1) ->
                 let uu____6380 = encode_formula _then env  in
                 (match uu____6380 with
                  | (t,decls2) ->
                      let uu____6387 = encode_formula _else env  in
                      (match uu____6387 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6396 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6415 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6415  in
      let connectives =
        let uu____6427 =
          let uu____6436 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6436)  in
        let uu____6449 =
          let uu____6459 =
            let uu____6468 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6468)  in
          let uu____6481 =
            let uu____6491 =
              let uu____6501 =
                let uu____6510 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6510)  in
              let uu____6523 =
                let uu____6533 =
                  let uu____6543 =
                    let uu____6552 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6552)  in
                  [uu____6543;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6533  in
              uu____6501 :: uu____6523  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6491  in
          uu____6459 :: uu____6481  in
        uu____6427 :: uu____6449  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6714 = encode_formula phi' env  in
            (match uu____6714 with
             | (phi2,decls) ->
                 let uu____6721 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6721, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6722 ->
            let uu____6727 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6727 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6756 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6756 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6764;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6766;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6782 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6782 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6814::(x,uu____6816)::(t,uu____6818)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6852 = encode_term x env  in
                 (match uu____6852 with
                  | (x1,decls) ->
                      let uu____6859 = encode_term t env  in
                      (match uu____6859 with
                       | (t1,decls') ->
                           let uu____6866 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6866, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6870)::(msg,uu____6872)::(phi2,uu____6874)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6908 =
                   let uu____6911 =
                     let uu____6912 = FStar_Syntax_Subst.compress r  in
                     uu____6912.FStar_Syntax_Syntax.n  in
                   let uu____6915 =
                     let uu____6916 = FStar_Syntax_Subst.compress msg  in
                     uu____6916.FStar_Syntax_Syntax.n  in
                   (uu____6911, uu____6915)  in
                 (match uu____6908 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6923))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6939 -> fallback phi2)
             | uu____6942 when head_redex env head2 ->
                 let uu____6950 = whnf env phi1  in
                 encode_formula uu____6950 env
             | uu____6951 ->
                 let uu____6959 = encode_term phi1 env  in
                 (match uu____6959 with
                  | (tt,decls) ->
                      let uu____6966 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6967 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6967.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6967.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6966, decls)))
        | uu____6970 ->
            let uu____6971 = encode_term phi1 env  in
            (match uu____6971 with
             | (tt,decls) ->
                 let uu____6978 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6979 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6979.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6979.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6978, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____7006 = encode_binders None bs env1  in
        match uu____7006 with
        | (vars,guards,env2,decls,uu____7028) ->
            let uu____7035 =
              let uu____7042 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7065 =
                          let uu____7070 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7084  ->
                                    match uu____7084 with
                                    | (t,uu____7090) ->
                                        encode_term t
                                          (let uu___152_7091 = env2  in
                                           {
                                             bindings =
                                               (uu___152_7091.bindings);
                                             depth = (uu___152_7091.depth);
                                             tcenv = (uu___152_7091.tcenv);
                                             warn = (uu___152_7091.warn);
                                             cache = (uu___152_7091.cache);
                                             nolabels =
                                               (uu___152_7091.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7091.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right uu____7070 FStar_List.unzip
                           in
                        match uu____7065 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7042 FStar_List.unzip  in
            (match uu____7035 with
             | (pats,decls') ->
                 let uu____7143 = encode_formula body env2  in
                 (match uu____7143 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7162;
                             FStar_SMTEncoding_Term.rng = uu____7163;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7171 -> guards  in
                      let uu____7174 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7174, body1,
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
                (fun uu____7208  ->
                   match uu____7208 with
                   | (x,uu____7212) ->
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
               let uu____7218 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7224 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7224) uu____7218 tl1
                in
             let uu____7226 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7238  ->
                       match uu____7238 with
                       | (b,uu____7242) ->
                           let uu____7243 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7243))
                in
             (match uu____7226 with
              | None  -> ()
              | Some (x,uu____7247) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7257 =
                    let uu____7258 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7258
                     in
                  FStar_Errors.warn pos uu____7257)
          in
       let uu____7259 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7259 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7265 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7301  ->
                     match uu____7301 with
                     | (l,uu____7311) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7265 with
            | None  -> fallback phi1
            | Some (uu____7334,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7363 = encode_q_body env vars pats body  in
             match uu____7363 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7389 =
                     let uu____7395 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7395)  in
                   FStar_SMTEncoding_Term.mkForall uu____7389
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7407 = encode_q_body env vars pats body  in
             match uu____7407 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7432 =
                   let uu____7433 =
                     let uu____7439 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7439)  in
                   FStar_SMTEncoding_Term.mkExists uu____7433
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7432, decls))))

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
  let uu____7488 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7488 with
  | (asym,a) ->
      let uu____7493 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7493 with
       | (xsym,x) ->
           let uu____7498 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7498 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7528 =
                      let uu____7534 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7534, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7528  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7549 =
                      let uu____7553 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7553)  in
                    FStar_SMTEncoding_Util.mkApp uu____7549  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7561 =
                    let uu____7563 =
                      let uu____7565 =
                        let uu____7567 =
                          let uu____7568 =
                            let uu____7573 =
                              let uu____7574 =
                                let uu____7580 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7580)  in
                              FStar_SMTEncoding_Util.mkForall uu____7574  in
                            (uu____7573, None,
                              (Some (Prims.strcat "primitive_" x1)))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7568  in
                        let uu____7590 =
                          let uu____7592 =
                            let uu____7593 =
                              let uu____7598 =
                                let uu____7599 =
                                  let uu____7605 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7605)  in
                                FStar_SMTEncoding_Util.mkForall uu____7599
                                 in
                              (uu____7598,
                                (Some "Name-token correspondence"),
                                (Some
                                   (Prims.strcat "token_correspondence_" x1)))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7593  in
                          [uu____7592]  in
                        uu____7567 :: uu____7590  in
                      xtok_decl :: uu____7565  in
                    xname_decl :: uu____7563  in
                  (xtok1, uu____7561)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7655 =
                    let uu____7663 =
                      let uu____7669 =
                        let uu____7670 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7670
                         in
                      quant axy uu____7669  in
                    (FStar_Syntax_Const.op_Eq, uu____7663)  in
                  let uu____7676 =
                    let uu____7685 =
                      let uu____7693 =
                        let uu____7699 =
                          let uu____7700 =
                            let uu____7701 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7701  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7700
                           in
                        quant axy uu____7699  in
                      (FStar_Syntax_Const.op_notEq, uu____7693)  in
                    let uu____7707 =
                      let uu____7716 =
                        let uu____7724 =
                          let uu____7730 =
                            let uu____7731 =
                              let uu____7732 =
                                let uu____7735 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7736 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7735, uu____7736)  in
                              FStar_SMTEncoding_Util.mkLT uu____7732  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7731
                             in
                          quant xy uu____7730  in
                        (FStar_Syntax_Const.op_LT, uu____7724)  in
                      let uu____7742 =
                        let uu____7751 =
                          let uu____7759 =
                            let uu____7765 =
                              let uu____7766 =
                                let uu____7767 =
                                  let uu____7770 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7771 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7770, uu____7771)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7767  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7766
                               in
                            quant xy uu____7765  in
                          (FStar_Syntax_Const.op_LTE, uu____7759)  in
                        let uu____7777 =
                          let uu____7786 =
                            let uu____7794 =
                              let uu____7800 =
                                let uu____7801 =
                                  let uu____7802 =
                                    let uu____7805 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7806 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7805, uu____7806)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7802  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7801
                                 in
                              quant xy uu____7800  in
                            (FStar_Syntax_Const.op_GT, uu____7794)  in
                          let uu____7812 =
                            let uu____7821 =
                              let uu____7829 =
                                let uu____7835 =
                                  let uu____7836 =
                                    let uu____7837 =
                                      let uu____7840 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7841 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7840, uu____7841)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7837
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7836
                                   in
                                quant xy uu____7835  in
                              (FStar_Syntax_Const.op_GTE, uu____7829)  in
                            let uu____7847 =
                              let uu____7856 =
                                let uu____7864 =
                                  let uu____7870 =
                                    let uu____7871 =
                                      let uu____7872 =
                                        let uu____7875 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7876 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7875, uu____7876)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7872
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7871
                                     in
                                  quant xy uu____7870  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7864)
                                 in
                              let uu____7882 =
                                let uu____7891 =
                                  let uu____7899 =
                                    let uu____7905 =
                                      let uu____7906 =
                                        let uu____7907 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7907
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7906
                                       in
                                    quant qx uu____7905  in
                                  (FStar_Syntax_Const.op_Minus, uu____7899)
                                   in
                                let uu____7913 =
                                  let uu____7922 =
                                    let uu____7930 =
                                      let uu____7936 =
                                        let uu____7937 =
                                          let uu____7938 =
                                            let uu____7941 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7942 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7941, uu____7942)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7938
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7937
                                         in
                                      quant xy uu____7936  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7930)
                                     in
                                  let uu____7948 =
                                    let uu____7957 =
                                      let uu____7965 =
                                        let uu____7971 =
                                          let uu____7972 =
                                            let uu____7973 =
                                              let uu____7976 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7977 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7976, uu____7977)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7973
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7972
                                           in
                                        quant xy uu____7971  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7965)
                                       in
                                    let uu____7983 =
                                      let uu____7992 =
                                        let uu____8000 =
                                          let uu____8006 =
                                            let uu____8007 =
                                              let uu____8008 =
                                                let uu____8011 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____8012 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____8011, uu____8012)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8008
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8007
                                             in
                                          quant xy uu____8006  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8000)
                                         in
                                      let uu____8018 =
                                        let uu____8027 =
                                          let uu____8035 =
                                            let uu____8041 =
                                              let uu____8042 =
                                                let uu____8043 =
                                                  let uu____8046 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8047 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8046, uu____8047)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8043
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8042
                                               in
                                            quant xy uu____8041  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8035)
                                           in
                                        let uu____8053 =
                                          let uu____8062 =
                                            let uu____8070 =
                                              let uu____8076 =
                                                let uu____8077 =
                                                  let uu____8078 =
                                                    let uu____8081 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8082 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8081, uu____8082)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8078
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8077
                                                 in
                                              quant xy uu____8076  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8070)
                                             in
                                          let uu____8088 =
                                            let uu____8097 =
                                              let uu____8105 =
                                                let uu____8111 =
                                                  let uu____8112 =
                                                    let uu____8113 =
                                                      let uu____8116 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8117 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8116,
                                                        uu____8117)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8113
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8112
                                                   in
                                                quant xy uu____8111  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8105)
                                               in
                                            let uu____8123 =
                                              let uu____8132 =
                                                let uu____8140 =
                                                  let uu____8146 =
                                                    let uu____8147 =
                                                      let uu____8148 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8148
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8147
                                                     in
                                                  quant qx uu____8146  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8140)
                                                 in
                                              [uu____8132]  in
                                            uu____8097 :: uu____8123  in
                                          uu____8062 :: uu____8088  in
                                        uu____8027 :: uu____8053  in
                                      uu____7992 :: uu____8018  in
                                    uu____7957 :: uu____7983  in
                                  uu____7922 :: uu____7948  in
                                uu____7891 :: uu____7913  in
                              uu____7856 :: uu____7882  in
                            uu____7821 :: uu____7847  in
                          uu____7786 :: uu____7812  in
                        uu____7751 :: uu____7777  in
                      uu____7716 :: uu____7742  in
                    uu____7685 :: uu____7707  in
                  uu____7655 :: uu____7676  in
                let mk1 l v1 =
                  let uu____8276 =
                    let uu____8281 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8313  ->
                              match uu____8313 with
                              | (l',uu____8322) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8281
                      (FStar_Option.map
                         (fun uu____8355  ->
                            match uu____8355 with | (uu____8366,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8276 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8407  ->
                          match uu____8407 with
                          | (l',uu____8416) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8439 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____8439 with
      | (xxsym,xx) ->
          let uu____8444 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____8444 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               let uu____8451 =
                 let uu____8456 =
                   let uu____8457 =
                     let uu____8463 =
                       let uu____8464 =
                         let uu____8467 =
                           let uu____8468 =
                             let uu____8471 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx])
                                in
                             (tapp, uu____8471)  in
                           FStar_SMTEncoding_Util.mkEq uu____8468  in
                         (xx_has_type, uu____8467)  in
                       FStar_SMTEncoding_Util.mkImp uu____8464  in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8463)
                      in
                   FStar_SMTEncoding_Util.mkForall uu____8457  in
                 let uu____8484 =
                   let uu____8486 =
                     let uu____8487 =
                       let uu____8488 = FStar_Util.digest_of_string tapp_hash
                          in
                       Prims.strcat "pretyping_" uu____8488  in
                     varops.mk_unique uu____8487  in
                   Some uu____8486  in
                 (uu____8456, (Some "pretyping"), uu____8484)  in
               FStar_SMTEncoding_Term.Assume uu____8451)
  
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
    let uu____8519 =
      let uu____8520 =
        let uu____8525 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8525, (Some "unit typing"), (Some "unit_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8520  in
    let uu____8528 =
      let uu____8530 =
        let uu____8531 =
          let uu____8536 =
            let uu____8537 =
              let uu____8543 =
                let uu____8544 =
                  let uu____8547 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8547)  in
                FStar_SMTEncoding_Util.mkImp uu____8544  in
              ([[typing_pred]], [xx], uu____8543)  in
            mkForall_fuel uu____8537  in
          (uu____8536, (Some "unit inversion"), (Some "unit_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8531  in
      [uu____8530]  in
    uu____8519 :: uu____8528  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8576 =
      let uu____8577 =
        let uu____8582 =
          let uu____8583 =
            let uu____8589 =
              let uu____8592 =
                let uu____8594 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8594]  in
              [uu____8592]  in
            let uu____8597 =
              let uu____8598 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8598 tt  in
            (uu____8589, [bb], uu____8597)  in
          FStar_SMTEncoding_Util.mkForall uu____8583  in
        (uu____8582, (Some "bool typing"), (Some "bool_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8577  in
    let uu____8610 =
      let uu____8612 =
        let uu____8613 =
          let uu____8618 =
            let uu____8619 =
              let uu____8625 =
                let uu____8626 =
                  let uu____8629 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8629)  in
                FStar_SMTEncoding_Util.mkImp uu____8626  in
              ([[typing_pred]], [xx], uu____8625)  in
            mkForall_fuel uu____8619  in
          (uu____8618, (Some "bool inversion"), (Some "bool_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8613  in
      [uu____8612]  in
    uu____8576 :: uu____8610  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8664 =
        let uu____8665 =
          let uu____8669 =
            let uu____8671 =
              let uu____8673 =
                let uu____8675 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8676 =
                  let uu____8678 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8678]  in
                uu____8675 :: uu____8676  in
              tt :: uu____8673  in
            tt :: uu____8671  in
          ("Prims.Precedes", uu____8669)  in
        FStar_SMTEncoding_Util.mkApp uu____8665  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8664  in
    let precedes_y_x =
      let uu____8681 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8681  in
    let uu____8683 =
      let uu____8684 =
        let uu____8689 =
          let uu____8690 =
            let uu____8696 =
              let uu____8699 =
                let uu____8701 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8701]  in
              [uu____8699]  in
            let uu____8704 =
              let uu____8705 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8705 tt  in
            (uu____8696, [bb], uu____8704)  in
          FStar_SMTEncoding_Util.mkForall uu____8690  in
        (uu____8689, (Some "int typing"), (Some "int_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8684  in
    let uu____8717 =
      let uu____8719 =
        let uu____8720 =
          let uu____8725 =
            let uu____8726 =
              let uu____8732 =
                let uu____8733 =
                  let uu____8736 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8736)  in
                FStar_SMTEncoding_Util.mkImp uu____8733  in
              ([[typing_pred]], [xx], uu____8732)  in
            mkForall_fuel uu____8726  in
          (uu____8725, (Some "int inversion"), (Some "int_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8720  in
      let uu____8750 =
        let uu____8752 =
          let uu____8753 =
            let uu____8758 =
              let uu____8759 =
                let uu____8765 =
                  let uu____8766 =
                    let uu____8769 =
                      let uu____8770 =
                        let uu____8772 =
                          let uu____8774 =
                            let uu____8776 =
                              let uu____8777 =
                                let uu____8780 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8781 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8780, uu____8781)  in
                              FStar_SMTEncoding_Util.mkGT uu____8777  in
                            let uu____8782 =
                              let uu____8784 =
                                let uu____8785 =
                                  let uu____8788 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8789 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8788, uu____8789)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8785  in
                              let uu____8790 =
                                let uu____8792 =
                                  let uu____8793 =
                                    let uu____8796 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8797 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8796, uu____8797)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8793  in
                                [uu____8792]  in
                              uu____8784 :: uu____8790  in
                            uu____8776 :: uu____8782  in
                          typing_pred_y :: uu____8774  in
                        typing_pred :: uu____8772  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8770  in
                    (uu____8769, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8766  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8765)
                 in
              mkForall_fuel uu____8759  in
            (uu____8758, (Some "well-founded ordering on nat (alt)"),
              (Some "well-founded-ordering-on-nat"))
             in
          FStar_SMTEncoding_Term.Assume uu____8753  in
        [uu____8752]  in
      uu____8719 :: uu____8750  in
    uu____8683 :: uu____8717  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8828 =
      let uu____8829 =
        let uu____8834 =
          let uu____8835 =
            let uu____8841 =
              let uu____8844 =
                let uu____8846 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8846]  in
              [uu____8844]  in
            let uu____8849 =
              let uu____8850 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8850 tt  in
            (uu____8841, [bb], uu____8849)  in
          FStar_SMTEncoding_Util.mkForall uu____8835  in
        (uu____8834, (Some "string typing"), (Some "string_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8829  in
    let uu____8862 =
      let uu____8864 =
        let uu____8865 =
          let uu____8870 =
            let uu____8871 =
              let uu____8877 =
                let uu____8878 =
                  let uu____8881 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8881)  in
                FStar_SMTEncoding_Util.mkImp uu____8878  in
              ([[typing_pred]], [xx], uu____8877)  in
            mkForall_fuel uu____8871  in
          (uu____8870, (Some "string inversion"), (Some "string_inversion"))
           in
        FStar_SMTEncoding_Term.Assume uu____8865  in
      [uu____8864]  in
    uu____8828 :: uu____8862  in
  let mk_ref1 env reft_name uu____8904 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8915 =
        let uu____8919 =
          let uu____8921 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8921]
           in
        (reft_name, uu____8919)  in
      FStar_SMTEncoding_Util.mkApp uu____8915  in
    let refb =
      let uu____8924 =
        let uu____8928 =
          let uu____8930 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8930]
           in
        (reft_name, uu____8928)  in
      FStar_SMTEncoding_Util.mkApp uu____8924  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8934 =
      let uu____8935 =
        let uu____8940 =
          let uu____8941 =
            let uu____8947 =
              let uu____8948 =
                let uu____8951 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8951)  in
              FStar_SMTEncoding_Util.mkImp uu____8948  in
            ([[typing_pred]], [xx; aa], uu____8947)  in
          mkForall_fuel uu____8941  in
        (uu____8940, (Some "ref inversion"), (Some "ref_inversion"))  in
      FStar_SMTEncoding_Term.Assume uu____8935  in
    let uu____8967 =
      let uu____8969 =
        let uu____8970 =
          let uu____8975 =
            let uu____8976 =
              let uu____8982 =
                let uu____8983 =
                  let uu____8986 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8987 =
                    let uu____8988 =
                      let uu____8991 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8992 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8991, uu____8992)  in
                    FStar_SMTEncoding_Util.mkEq uu____8988  in
                  (uu____8986, uu____8987)  in
                FStar_SMTEncoding_Util.mkImp uu____8983  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8982)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8976  in
          (uu____8975, (Some "ref typing is injective"),
            (Some "ref_injectivity"))
           in
        FStar_SMTEncoding_Term.Assume uu____8970  in
      [uu____8969]  in
    uu____8934 :: uu____8967  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____9036 =
      let uu____9037 =
        let uu____9042 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9042, (Some "False interpretation"), (Some "false_interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____9037  in
    [uu____9036]  in
  let mk_and_interp env conj uu____9054 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9064 =
        let uu____9068 =
          let uu____9070 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____9070]  in
        ("Valid", uu____9068)  in
      FStar_SMTEncoding_Util.mkApp uu____9064  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9077 =
      let uu____9078 =
        let uu____9083 =
          let uu____9084 =
            let uu____9090 =
              let uu____9091 =
                let uu____9094 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9094, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9091  in
            ([[valid]], [aa; bb], uu____9090)  in
          FStar_SMTEncoding_Util.mkForall uu____9084  in
        (uu____9083, (Some "/\\ interpretation"), (Some "l_and-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9078  in
    [uu____9077]  in
  let mk_or_interp env disj uu____9119 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9129 =
        let uu____9133 =
          let uu____9135 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____9135]  in
        ("Valid", uu____9133)  in
      FStar_SMTEncoding_Util.mkApp uu____9129  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9142 =
      let uu____9143 =
        let uu____9148 =
          let uu____9149 =
            let uu____9155 =
              let uu____9156 =
                let uu____9159 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9159, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9156  in
            ([[valid]], [aa; bb], uu____9155)  in
          FStar_SMTEncoding_Util.mkForall uu____9149  in
        (uu____9148, (Some "\\/ interpretation"), (Some "l_or-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9143  in
    [uu____9142]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9198 =
        let uu____9202 =
          let uu____9204 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____9204]  in
        ("Valid", uu____9202)  in
      FStar_SMTEncoding_Util.mkApp uu____9198  in
    let uu____9207 =
      let uu____9208 =
        let uu____9213 =
          let uu____9214 =
            let uu____9220 =
              let uu____9221 =
                let uu____9224 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9224, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9221  in
            ([[valid]], [aa; xx1; yy1], uu____9220)  in
          FStar_SMTEncoding_Util.mkForall uu____9214  in
        (uu____9213, (Some "Eq2 interpretation"), (Some "eq2-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9208  in
    [uu____9207]  in
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
      let uu____9269 =
        let uu____9273 =
          let uu____9275 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____9275]  in
        ("Valid", uu____9273)  in
      FStar_SMTEncoding_Util.mkApp uu____9269  in
    let uu____9278 =
      let uu____9279 =
        let uu____9284 =
          let uu____9285 =
            let uu____9291 =
              let uu____9292 =
                let uu____9295 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9295, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9292  in
            ([[valid]], [aa; bb; xx1; yy1], uu____9291)  in
          FStar_SMTEncoding_Util.mkForall uu____9285  in
        (uu____9284, (Some "Eq3 interpretation"), (Some "eq3-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9279  in
    [uu____9278]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9334 =
        let uu____9338 =
          let uu____9340 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____9340]  in
        ("Valid", uu____9338)  in
      FStar_SMTEncoding_Util.mkApp uu____9334  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9347 =
      let uu____9348 =
        let uu____9353 =
          let uu____9354 =
            let uu____9360 =
              let uu____9361 =
                let uu____9364 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9364, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9361  in
            ([[valid]], [aa; bb], uu____9360)  in
          FStar_SMTEncoding_Util.mkForall uu____9354  in
        (uu____9353, (Some "==> interpretation"), (Some "l_imp-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9348  in
    [uu____9347]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9399 =
        let uu____9403 =
          let uu____9405 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9405]  in
        ("Valid", uu____9403)  in
      FStar_SMTEncoding_Util.mkApp uu____9399  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9412 =
      let uu____9413 =
        let uu____9418 =
          let uu____9419 =
            let uu____9425 =
              let uu____9426 =
                let uu____9429 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9429, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9426  in
            ([[valid]], [aa; bb], uu____9425)  in
          FStar_SMTEncoding_Util.mkForall uu____9419  in
        (uu____9418, (Some "<==> interpretation"), (Some "l_iff-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9413  in
    [uu____9412]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9460 =
        let uu____9464 =
          let uu____9466 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9466]  in
        ("Valid", uu____9464)  in
      FStar_SMTEncoding_Util.mkApp uu____9460  in
    let not_valid_a =
      let uu____9470 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9470  in
    let uu____9472 =
      let uu____9473 =
        let uu____9478 =
          let uu____9479 =
            let uu____9485 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9485)  in
          FStar_SMTEncoding_Util.mkForall uu____9479  in
        (uu____9478, (Some "not interpretation"), (Some "l_not-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9473  in
    [uu____9472]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9522 =
        let uu____9526 =
          let uu____9528 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9528]  in
        ("Valid", uu____9526)  in
      FStar_SMTEncoding_Util.mkApp uu____9522  in
    let valid_b_x =
      let uu____9532 =
        let uu____9536 =
          let uu____9538 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9538]  in
        ("Valid", uu____9536)  in
      FStar_SMTEncoding_Util.mkApp uu____9532  in
    let uu____9540 =
      let uu____9541 =
        let uu____9546 =
          let uu____9547 =
            let uu____9553 =
              let uu____9554 =
                let uu____9557 =
                  let uu____9558 =
                    let uu____9564 =
                      let uu____9567 =
                        let uu____9569 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9569]  in
                      [uu____9567]  in
                    let uu____9572 =
                      let uu____9573 =
                        let uu____9576 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9576, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9573  in
                    (uu____9564, [xx1], uu____9572)  in
                  FStar_SMTEncoding_Util.mkForall uu____9558  in
                (uu____9557, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9554  in
            ([[valid]], [aa; bb], uu____9553)  in
          FStar_SMTEncoding_Util.mkForall uu____9547  in
        (uu____9546, (Some "forall interpretation"), (Some "forall-interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____9541  in
    [uu____9540]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9624 =
        let uu____9628 =
          let uu____9630 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9630]  in
        ("Valid", uu____9628)  in
      FStar_SMTEncoding_Util.mkApp uu____9624  in
    let valid_b_x =
      let uu____9634 =
        let uu____9638 =
          let uu____9640 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9640]  in
        ("Valid", uu____9638)  in
      FStar_SMTEncoding_Util.mkApp uu____9634  in
    let uu____9642 =
      let uu____9643 =
        let uu____9648 =
          let uu____9649 =
            let uu____9655 =
              let uu____9656 =
                let uu____9659 =
                  let uu____9660 =
                    let uu____9666 =
                      let uu____9669 =
                        let uu____9671 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9671]  in
                      [uu____9669]  in
                    let uu____9674 =
                      let uu____9675 =
                        let uu____9678 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9678, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9675  in
                    (uu____9666, [xx1], uu____9674)  in
                  FStar_SMTEncoding_Util.mkExists uu____9660  in
                (uu____9659, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9656  in
            ([[valid]], [aa; bb], uu____9655)  in
          FStar_SMTEncoding_Util.mkForall uu____9649  in
        (uu____9648, (Some "exists interpretation"), (Some "exists-interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____9643  in
    [uu____9642]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9715 =
      let uu____9716 =
        let uu____9721 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9722 =
          let uu____9724 = varops.mk_unique "typing_range_const"  in
          Some uu____9724  in
        (uu____9721, (Some "Range_const typing"), uu____9722)  in
      FStar_SMTEncoding_Term.Assume uu____9716  in
    [uu____9715]  in
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
          let uu____9987 =
            FStar_Util.find_opt
              (fun uu____10005  ->
                 match uu____10005 with
                 | (l,uu____10015) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9987 with
          | None  -> []
          | Some (uu____10037,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____10074 = encode_function_type_as_formula None None t env  in
        match uu____10074 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Term.Assume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Some (Prims.strcat "lemma_" lid.FStar_Ident.str)))]
  
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
            let uu____10107 =
              (let uu____10108 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10108) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10107
            then
              let uu____10112 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10112 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10124 =
                      let uu____10125 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10125.FStar_Syntax_Syntax.n  in
                    match uu____10124 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10130) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10147  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10150 -> []  in
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
              (let uu____10159 = prims.is lid  in
               if uu____10159
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10164 = prims.mk lid vname  in
                 match uu____10164 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10179 =
                    let uu____10185 = curried_arrow_formals_comp t_norm  in
                    match uu____10185 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10196 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10196
                          then
                            let uu____10197 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10198 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10198.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10198.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10198.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10198.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10198.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10198.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10198.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10198.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10198.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10198.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10198.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10198.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10198.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10198.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10198.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10198.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10198.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10198.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10198.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10198.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10198.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10198.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10198.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10197
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10205 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10205)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10179 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10232 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10232 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10245 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10269  ->
                                     match uu___124_10269 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10272 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10272 with
                                          | (uu____10283,(xxsym,uu____10285))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10295 =
                                                let uu____10296 =
                                                  let uu____10301 =
                                                    let uu____10302 =
                                                      let uu____10308 =
                                                        let uu____10309 =
                                                          let uu____10312 =
                                                            let uu____10313 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10313
                                                             in
                                                          (vapp, uu____10312)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10309
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10308)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10302
                                                     in
                                                  (uu____10301,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "disc_equation_"
                                                          (escape
                                                             d.FStar_Ident.str))))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10296
                                                 in
                                              [uu____10295])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10325 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10325 with
                                          | (uu____10336,(xxsym,uu____10338))
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
                                              let uu____10352 =
                                                let uu____10353 =
                                                  let uu____10358 =
                                                    let uu____10359 =
                                                      let uu____10365 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10365)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10359
                                                     in
                                                  (uu____10358,
                                                    (Some
                                                       "Projector equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "proj_equation_"
                                                          tp_name)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10353
                                                 in
                                              [uu____10352])
                                     | uu____10375 -> []))
                              in
                           let uu____10376 = encode_binders None formals env1
                              in
                           (match uu____10376 with
                            | (vars,guards,env',decls1,uu____10392) ->
                                let uu____10399 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10404 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10404, decls1)
                                  | Some p ->
                                      let uu____10406 = encode_formula p env'
                                         in
                                      (match uu____10406 with
                                       | (g,ds) ->
                                           let uu____10413 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10413,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10399 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10422 =
                                         let uu____10426 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10426)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10422
                                        in
                                     let uu____10431 =
                                       let vname_decl =
                                         let uu____10436 =
                                           let uu____10442 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10447  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10442,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10436
                                          in
                                       let uu____10452 =
                                         let env2 =
                                           let uu___154_10456 = env1  in
                                           {
                                             bindings =
                                               (uu___154_10456.bindings);
                                             depth = (uu___154_10456.depth);
                                             tcenv = (uu___154_10456.tcenv);
                                             warn = (uu___154_10456.warn);
                                             cache = (uu___154_10456.cache);
                                             nolabels =
                                               (uu___154_10456.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10456.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____10457 =
                                           let uu____10458 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10458  in
                                         if uu____10457
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10452 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             FStar_SMTEncoding_Term.Assume
                                               (tok_typing,
                                                 (Some
                                                    "function token typing"),
                                                 (Some
                                                    (Prims.strcat
                                                       "function_token_typing_"
                                                       vname)))
                                              in
                                           let uu____10470 =
                                             match formals with
                                             | [] ->
                                                 let uu____10479 =
                                                   let uu____10480 =
                                                     let uu____10482 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10482
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10480
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10479)
                                             | uu____10485 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10490 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10490
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10492 =
                                                     let uu____10497 =
                                                       let uu____10498 =
                                                         let uu____10504 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10504)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10498
                                                        in
                                                     (uu____10497,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Some
                                                          (Prims.strcat
                                                             "token_correspondence_"
                                                             vname)))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10492
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10470 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10431 with
                                      | (decls2,env2) ->
                                          let uu____10529 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10534 =
                                              encode_term res_t1 env'  in
                                            match uu____10534 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10542 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10542,
                                                  decls)
                                             in
                                          (match uu____10529 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10550 =
                                                   let uu____10555 =
                                                     let uu____10556 =
                                                       let uu____10562 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10562)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10556
                                                      in
                                                   (uu____10555,
                                                     (Some "free var typing"),
                                                     (Some
                                                        (Prims.strcat
                                                           "typing_" vname)))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10550
                                                  in
                                               let freshness =
                                                 let uu____10572 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10572
                                                 then
                                                   let uu____10575 =
                                                     let uu____10576 =
                                                       let uu____10582 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10588 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10582,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10588)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10576
                                                      in
                                                   let uu____10590 =
                                                     let uu____10592 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [uu____10592]  in
                                                   uu____10575 :: uu____10590
                                                 else []  in
                                               let g =
                                                 let uu____10596 =
                                                   let uu____10598 =
                                                     let uu____10600 =
                                                       let uu____10602 =
                                                         let uu____10604 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10604
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10602
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10600
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10598
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10596
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
          let uu____10626 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10626 with
          | None  ->
              let uu____10649 = encode_free_var env x t t_norm []  in
              (match uu____10649 with
               | (decls,env1) ->
                   let uu____10664 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10664 with
                    | (n1,x',uu____10683) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10695) -> ((n1, x1), [], env)
  
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
          let uu____10728 = encode_free_var env lid t tt quals  in
          match uu____10728 with
          | (decls,env1) ->
              let uu____10739 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10739
              then
                let uu____10743 =
                  let uu____10745 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10745  in
                (uu____10743, env1)
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
             (fun uu____10773  ->
                fun lb  ->
                  match uu____10773 with
                  | (decls,env1) ->
                      let uu____10785 =
                        let uu____10789 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10789
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10785 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10803 = FStar_Syntax_Util.head_and_args t  in
    match uu____10803 with
    | (hd1,args) ->
        let uu____10829 =
          let uu____10830 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10830.FStar_Syntax_Syntax.n  in
        (match uu____10829 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10834,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10847 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10862  ->
      fun quals  ->
        match uu____10862 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10911 = FStar_Util.first_N nbinders formals  in
              match uu____10911 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10951  ->
                         fun uu____10952  ->
                           match (uu____10951, uu____10952) with
                           | ((formal,uu____10962),(binder,uu____10964)) ->
                               let uu____10969 =
                                 let uu____10974 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10974)  in
                               FStar_Syntax_Syntax.NT uu____10969) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10979 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10993  ->
                              match uu____10993 with
                              | (x,i) ->
                                  let uu____11000 =
                                    let uu___155_11001 = x  in
                                    let uu____11002 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_11001.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_11001.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11002
                                    }  in
                                  (uu____11000, i)))
                       in
                    FStar_All.pipe_right uu____10979
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____11014 =
                      let uu____11016 =
                        let uu____11017 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____11017.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11016
                       in
                    let uu____11021 =
                      let uu____11022 = FStar_Syntax_Subst.compress body  in
                      let uu____11023 =
                        let uu____11024 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____11024  in
                      FStar_Syntax_Syntax.extend_app_n uu____11022
                        uu____11023
                       in
                    uu____11021 uu____11014 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11066 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____11066
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11067 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11067.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11067.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11067.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11067.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11067.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11067.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11067.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11067.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11067.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11067.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11067.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11067.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11067.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11067.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11067.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11067.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11067.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11067.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11067.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11067.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11067.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11067.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11067.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____11088 = FStar_Syntax_Util.abs_formals e  in
                match uu____11088 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11137::uu____11138 ->
                         let uu____11146 =
                           let uu____11147 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11147.FStar_Syntax_Syntax.n  in
                         (match uu____11146 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11174 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11174 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11200 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11200
                                   then
                                     let uu____11218 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11218 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11264  ->
                                                   fun uu____11265  ->
                                                     match (uu____11264,
                                                             uu____11265)
                                                     with
                                                     | ((x,uu____11275),
                                                        (b,uu____11277)) ->
                                                         let uu____11282 =
                                                           let uu____11287 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11287)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11282)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11289 =
                                            let uu____11300 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11300)
                                             in
                                          (uu____11289, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11335 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11335 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11387) ->
                              let uu____11392 =
                                let uu____11403 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11403  in
                              (uu____11392, true)
                          | uu____11436 when Prims.op_Negation norm1 ->
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
                          | uu____11438 ->
                              let uu____11439 =
                                let uu____11440 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11441 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11440
                                  uu____11441
                                 in
                              failwith uu____11439)
                     | uu____11454 ->
                         let uu____11455 =
                           let uu____11456 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11456.FStar_Syntax_Syntax.n  in
                         (match uu____11455 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11483 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11483 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11501 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11501 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11549 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11577 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11577
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11584 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11625  ->
                            fun lb  ->
                              match uu____11625 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11676 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11676
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11679 =
                                      let uu____11687 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11687
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11679 with
                                    | (tok,decl,env2) ->
                                        let uu____11712 =
                                          let uu____11719 =
                                            let uu____11725 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11725, tok)  in
                                          uu____11719 :: toks  in
                                        (uu____11712, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11584 with
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
                        | uu____11827 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11832 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11832 vars)
                            else
                              (let uu____11834 =
                                 let uu____11838 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11838)  in
                               FStar_SMTEncoding_Util.mkApp uu____11834)
                         in
                      let uu____11843 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11845  ->
                                 match uu___125_11845 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11846 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11849 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11849)))
                         in
                      if uu____11843
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11869;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11871;
                                FStar_Syntax_Syntax.lbeff = uu____11872;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11913 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____11913 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11928 = env1  in
                                      let uu____11929 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1
                                         in
                                      {
                                        bindings = (uu___159_11928.bindings);
                                        depth = (uu___159_11928.depth);
                                        tcenv = uu____11929;
                                        warn = (uu___159_11928.warn);
                                        cache = (uu___159_11928.cache);
                                        nolabels = (uu___159_11928.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11928.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11928.encode_non_total_function_typ)
                                      }  in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e1 =
                                      let uu____11932 =
                                        FStar_Syntax_Subst.subst univ_subst e
                                         in
                                      FStar_Syntax_Subst.compress uu____11932
                                       in
                                    let uu____11933 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____11933 with
                                     | ((binders,body,uu____11945,uu____11946),curry)
                                         ->
                                         ((let uu____11953 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____11953
                                           then
                                             let uu____11954 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____11955 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11954 uu____11955
                                           else ());
                                          (let uu____11957 =
                                             encode_binders None binders env'
                                              in
                                           match uu____11957 with
                                           | (vars,guards,env'1,binder_decls,uu____11973)
                                               ->
                                               let body1 =
                                                 let uu____11981 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____11981
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____11984 =
                                                 let uu____11989 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____11989
                                                 then
                                                   let uu____11995 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____11996 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____11995, uu____11996)
                                                 else
                                                   (let uu____12002 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____12002))
                                                  in
                                               (match uu____11984 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12016 =
                                                        let uu____12021 =
                                                          let uu____12022 =
                                                            let uu____12028 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____12028)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12022
                                                           in
                                                        let uu____12034 =
                                                          let uu____12036 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____12036
                                                           in
                                                        (uu____12021,
                                                          uu____12034,
                                                          (Some
                                                             (Prims.strcat
                                                                "equation_" f)))
                                                         in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____12016
                                                       in
                                                    let uu____12039 =
                                                      let uu____12041 =
                                                        let uu____12043 =
                                                          let uu____12045 =
                                                            let uu____12047 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12047
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12045
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12043
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____12041
                                                       in
                                                    (uu____12039, env1))))))
                           | uu____12050 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12069 = varops.fresh "fuel"  in
                             (uu____12069, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____12072 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12111  ->
                                     fun uu____12112  ->
                                       match (uu____12111, uu____12112) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12194 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12194  in
                                           let gtok =
                                             let uu____12196 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12196  in
                                           let env3 =
                                             let uu____12198 =
                                               let uu____12200 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12200
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12198
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____12072 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12284
                                 t_norm uu____12286 =
                                 match (uu____12284, uu____12286) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12311;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12312;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12329 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____12329 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12346 = env2  in
                                            let uu____12347 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1
                                               in
                                            {
                                              bindings =
                                                (uu___160_12346.bindings);
                                              depth = (uu___160_12346.depth);
                                              tcenv = uu____12347;
                                              warn = (uu___160_12346.warn);
                                              cache = (uu___160_12346.cache);
                                              nolabels =
                                                (uu___160_12346.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12346.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12346.encode_non_total_function_typ)
                                            }  in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____12351 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12351
                                            then
                                              let uu____12352 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12353 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12354 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12352 uu____12353
                                                uu____12354
                                            else ());
                                           (let uu____12356 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12356 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12378 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12378
                                                  then
                                                    let uu____12379 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12380 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12381 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12382 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12379 uu____12380
                                                      uu____12381 uu____12382
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12386 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12386 with
                                                  | (vars,guards,env'1,binder_decls,uu____12404)
                                                      ->
                                                      let decl_g =
                                                        let uu____12412 =
                                                          let uu____12418 =
                                                            let uu____12420 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12420
                                                             in
                                                          (g, uu____12418,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12412
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
                                                        let uu____12435 =
                                                          let uu____12439 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12439)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12435
                                                         in
                                                      let gsapp =
                                                        let uu____12445 =
                                                          let uu____12449 =
                                                            let uu____12451 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12451 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12449)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12445
                                                         in
                                                      let gmax =
                                                        let uu____12455 =
                                                          let uu____12459 =
                                                            let uu____12461 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12461 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12459)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12455
                                                         in
                                                      let body1 =
                                                        let uu____12465 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12465
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12467 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12467 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12478
                                                               =
                                                               let uu____12483
                                                                 =
                                                                 let uu____12484
                                                                   =
                                                                   let uu____12492
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
                                                                    uu____12492)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12484
                                                                  in
                                                               let uu____12503
                                                                 =
                                                                 let uu____12505
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____12505
                                                                  in
                                                               (uu____12483,
                                                                 uu____12503,
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12478
                                                              in
                                                           let eqn_f =
                                                             let uu____12509
                                                               =
                                                               let uu____12514
                                                                 =
                                                                 let uu____12515
                                                                   =
                                                                   let uu____12521
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12521)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12515
                                                                  in
                                                               (uu____12514,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g)))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12509
                                                              in
                                                           let eqn_g' =
                                                             let uu____12530
                                                               =
                                                               let uu____12535
                                                                 =
                                                                 let uu____12536
                                                                   =
                                                                   let uu____12542
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12546
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    let uu____12551
                                                                    =
                                                                    let uu____12553
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12553
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12551)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12547
                                                                     in
                                                                    (gsapp,
                                                                    uu____12546)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12543
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12542)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12536
                                                                  in
                                                               (uu____12535,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Some
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g)))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12530
                                                              in
                                                           let uu____12566 =
                                                             let uu____12571
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12571
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12588)
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
                                                                    let uu____12603
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12603
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12606
                                                                    =
                                                                    let uu____12611
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    let uu____12618
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12618)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12612
                                                                     in
                                                                    (uu____12611,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)))
                                                                     in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12606
                                                                    in
                                                                 let uu____12630
                                                                   =
                                                                   let uu____12634
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12634
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12642
                                                                    =
                                                                    let uu____12644
                                                                    =
                                                                    let uu____12645
                                                                    =
                                                                    let uu____12650
                                                                    =
                                                                    let uu____12651
                                                                    =
                                                                    let uu____12657
                                                                    =
                                                                    let uu____12658
                                                                    =
                                                                    let uu____12661
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12661,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12658
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12657)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12651
                                                                     in
                                                                    (uu____12650,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12645
                                                                     in
                                                                    [uu____12644]
                                                                     in
                                                                    (d3,
                                                                    uu____12642)
                                                                    in
                                                                 (match uu____12630
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
                                                           (match uu____12566
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
                               let uu____12697 =
                                 let uu____12704 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12736  ->
                                      fun uu____12737  ->
                                        match (uu____12736, uu____12737) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12813 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12813 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12704
                                  in
                               (match uu____12697 with
                                | (decls2,eqns,env01) ->
                                    let uu____12853 =
                                      let isDeclFun uu___126_12861 =
                                        match uu___126_12861 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12862 -> true
                                        | uu____12868 -> false  in
                                      let uu____12869 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12869
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____12853 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12896 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12896
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
      (let uu____12929 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12929
       then
         let uu____12930 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12930
       else ());
      (let nm =
         let uu____12933 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12933 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12936 = encode_sigelt' env se  in
       match uu____12936 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12945 =
                  let uu____12947 =
                    let uu____12948 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12948  in
                  [uu____12947]  in
                (uu____12945, e)
            | uu____12950 ->
                let uu____12951 =
                  let uu____12953 =
                    let uu____12955 =
                      let uu____12956 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12956  in
                    uu____12955 :: g  in
                  let uu____12957 =
                    let uu____12959 =
                      let uu____12960 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12960  in
                    [uu____12959]  in
                  FStar_List.append uu____12953 uu____12957  in
                (uu____12951, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12968 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12977 =
            let uu____12978 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12978 Prims.op_Negation  in
          if uu____12977
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12998 ->
                   let uu____12999 =
                     let uu____13002 =
                       let uu____13003 =
                         let uu____13018 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13018)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____13003  in
                     FStar_Syntax_Syntax.mk uu____13002  in
                   uu____12999 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____13071 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____13071 with
               | (aname,atok,env2) ->
                   let uu____13081 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____13081 with
                    | (formals,uu____13091) ->
                        let uu____13098 =
                          let uu____13101 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____13101 env2  in
                        (match uu____13098 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13109 =
                                 let uu____13110 =
                                   let uu____13116 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13124  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13116,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____13110
                                  in
                               [uu____13109;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13131 =
                               let aux uu____13160 uu____13161 =
                                 match (uu____13160, uu____13161) with
                                 | ((bv,uu____13188),(env3,acc_sorts,acc)) ->
                                     let uu____13209 = gen_term_var env3 bv
                                        in
                                     (match uu____13209 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13131 with
                              | (uu____13247,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13261 =
                                      let uu____13266 =
                                        let uu____13267 =
                                          let uu____13273 =
                                            let uu____13274 =
                                              let uu____13277 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13277)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13274
                                             in
                                          ([[app]], xs_sorts, uu____13273)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13267
                                         in
                                      (uu____13266, (Some "Action equality"),
                                        (Some
                                           (Prims.strcat aname "_equality")))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13261
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13290 =
                                      let uu____13295 =
                                        let uu____13296 =
                                          let uu____13302 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13302)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13296
                                         in
                                      (uu____13295,
                                        (Some "Action token correspondence"),
                                        (Some
                                           (Prims.strcat aname
                                              "_token_correspondence")))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13290
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13313 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13313 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13329,uu____13330,uu____13331) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13334 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13334 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13345,t,quals) ->
          let will_encode_definition =
            let uu____13351 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13353  ->
                      match uu___127_13353 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13356 -> false))
               in
            Prims.op_Negation uu____13351  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13362 = encode_top_level_val env fv t quals  in
             match uu____13362 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13374 =
                   let uu____13376 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13376  in
                 (uu____13374, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13381) ->
          let uu____13384 = encode_formula f env  in
          (match uu____13384 with
           | (f1,decls) ->
               let g =
                 let uu____13393 =
                   let uu____13394 =
                     let uu____13399 =
                       let uu____13401 =
                         let uu____13402 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13402  in
                       Some uu____13401  in
                     let uu____13403 =
                       let uu____13405 =
                         varops.mk_unique
                           (Prims.strcat "assumption_" l.FStar_Ident.str)
                          in
                       Some uu____13405  in
                     (f1, uu____13399, uu____13403)  in
                   FStar_SMTEncoding_Term.Assume uu____13394  in
                 [uu____13393]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13410,quals,uu____13412) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13420 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13427 =
                       let uu____13432 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13432.FStar_Syntax_Syntax.fv_name  in
                     uu____13427.FStar_Syntax_Syntax.v  in
                   let uu____13436 =
                     let uu____13437 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13437  in
                   if uu____13436
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
                     let uu____13456 = encode_sigelt' env1 val_decl  in
                     match uu____13456 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____13420 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13473,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13475;
                          FStar_Syntax_Syntax.lbtyp = uu____13476;
                          FStar_Syntax_Syntax.lbeff = uu____13477;
                          FStar_Syntax_Syntax.lbdef = uu____13478;_}::[]),uu____13479,uu____13480,uu____13481)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13497 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13497 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13515 =
                   let uu____13519 =
                     let uu____13521 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13521]  in
                   ("Valid", uu____13519)  in
                 FStar_SMTEncoding_Util.mkApp uu____13515  in
               let decls =
                 let uu____13526 =
                   let uu____13528 =
                     let uu____13529 =
                       let uu____13534 =
                         let uu____13535 =
                           let uu____13541 =
                             let uu____13542 =
                               let uu____13545 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13545)  in
                             FStar_SMTEncoding_Util.mkEq uu____13542  in
                           ([[valid_b2t_x]], [xx], uu____13541)  in
                         FStar_SMTEncoding_Util.mkForall uu____13535  in
                       (uu____13534, (Some "b2t def"), (Some "b2t_def"))  in
                     FStar_SMTEncoding_Term.Assume uu____13529  in
                   [uu____13528]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13526
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13563,uu____13564,quals,uu____13566) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13574  ->
                  match uu___128_13574 with
                  | FStar_Syntax_Syntax.Discriminator uu____13575 -> true
                  | uu____13576 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13578,lids,quals,uu____13581) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13590 =
                     let uu____13591 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13591.FStar_Ident.idText  in
                   uu____13590 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13593  ->
                     match uu___129_13593 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13594 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13597,quals,uu____13599) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13611  ->
                  match uu___130_13611 with
                  | FStar_Syntax_Syntax.Projector uu____13612 -> true
                  | uu____13615 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13622 = try_lookup_free_var env l  in
          (match uu____13622 with
           | Some uu____13626 -> ([], env)
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
          ((is_rec,bindings),uu____13635,quals,uu____13637) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13651,uu____13652) ->
          let uu____13659 = encode_signature env ses  in
          (match uu____13659 with
           | (g,env1) ->
               let uu____13669 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13679  ->
                         match uu___131_13679 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13680,Some "inversion axiom",uu____13681)
                             -> false
                         | uu____13685 -> true))
                  in
               (match uu____13669 with
                | (g',inversions) ->
                    let uu____13694 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13704  ->
                              match uu___132_13704 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13705 ->
                                  true
                              | uu____13711 -> false))
                       in
                    (match uu____13694 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13722,tps,k,uu____13725,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13736  ->
                    match uu___133_13736 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13737 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13744 = c  in
              match uu____13744 with
              | (name,args,uu____13748,uu____13749,uu____13750) ->
                  let uu____13753 =
                    let uu____13754 =
                      let uu____13760 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13767  ->
                                match uu____13767 with
                                | (uu____13771,sort,uu____13773) -> sort))
                         in
                      (name, uu____13760, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13754  in
                  [uu____13753]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13791 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13794 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13794 FStar_Option.isNone))
               in
            if uu____13791
            then []
            else
              (let uu____13811 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13811 with
               | (xxsym,xx) ->
                   let uu____13817 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13828  ->
                             fun l  ->
                               match uu____13828 with
                               | (out,decls) ->
                                   let uu____13840 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13840 with
                                    | (uu____13846,data_t) ->
                                        let uu____13848 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13848 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13877 =
                                                 let uu____13878 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13878.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13877 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13886,indices) ->
                                                   indices
                                               | uu____13902 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13914  ->
                                                         match uu____13914
                                                         with
                                                         | (x,uu____13918) ->
                                                             let uu____13919
                                                               =
                                                               let uu____13920
                                                                 =
                                                                 let uu____13924
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13924,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13920
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13919)
                                                    env)
                                                in
                                             let uu____13926 =
                                               encode_args indices env1  in
                                             (match uu____13926 with
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
                                                      let uu____13946 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13954
                                                                 =
                                                                 let uu____13957
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13957,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13954)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13946
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13959 =
                                                      let uu____13960 =
                                                        let uu____13963 =
                                                          let uu____13964 =
                                                            let uu____13967 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13967,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13964
                                                           in
                                                        (out, uu____13963)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13960
                                                       in
                                                    (uu____13959,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13817 with
                    | (data_ax,decls) ->
                        let uu____13975 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13975 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13986 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13986 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13989 =
                                 let uu____13994 =
                                   let uu____13995 =
                                     let uu____14001 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____14009 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____14001,
                                       uu____14009)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13995
                                    in
                                 let uu____14017 =
                                   let uu____14019 =
                                     varops.mk_unique
                                       (Prims.strcat
                                          "fuel_guarded_inversion_"
                                          t.FStar_Ident.str)
                                      in
                                   Some uu____14019  in
                                 (uu____13994, (Some "inversion axiom"),
                                   uu____14017)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13989  in
                             let pattern_guarded_inversion =
                               let uu____14024 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____14024
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____14032 =
                                   let uu____14033 =
                                     let uu____14038 =
                                       let uu____14039 =
                                         let uu____14045 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____14053 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14045, uu____14053)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14039
                                        in
                                     let uu____14061 =
                                       let uu____14063 =
                                         varops.mk_unique
                                           (Prims.strcat
                                              "pattern_guarded_inversion_"
                                              t.FStar_Ident.str)
                                          in
                                       Some uu____14063  in
                                     (uu____14038, (Some "inversion axiom"),
                                       uu____14061)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____14033
                                    in
                                 [uu____14032]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____14067 =
            let uu____14075 =
              let uu____14076 = FStar_Syntax_Subst.compress k  in
              uu____14076.FStar_Syntax_Syntax.n  in
            match uu____14075 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14105 -> (tps, k)  in
          (match uu____14067 with
           | (formals,res) ->
               let uu____14120 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____14120 with
                | (formals1,res1) ->
                    let uu____14127 = encode_binders None formals1 env  in
                    (match uu____14127 with
                     | (vars,guards,env',binder_decls,uu____14142) ->
                         let uu____14149 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14149 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14162 =
                                  let uu____14166 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14166)  in
                                FStar_SMTEncoding_Util.mkApp uu____14162  in
                              let uu____14171 =
                                let tname_decl =
                                  let uu____14177 =
                                    let uu____14178 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14193  ->
                                              match uu____14193 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14201 = varops.next_id ()  in
                                    (tname, uu____14178,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14201, false)
                                     in
                                  constructor_or_logic_type_decl uu____14177
                                   in
                                let uu____14206 =
                                  match vars with
                                  | [] ->
                                      let uu____14213 =
                                        let uu____14214 =
                                          let uu____14216 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14216
                                           in
                                        push_free_var env1 t tname
                                          uu____14214
                                         in
                                      ([], uu____14213)
                                  | uu____14220 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14226 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14226
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14235 =
                                          let uu____14240 =
                                            let uu____14241 =
                                              let uu____14249 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14249)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14241
                                             in
                                          (uu____14240,
                                            (Some "name-token correspondence"),
                                            (Some
                                               (Prims.strcat
                                                  "token_correspondence_"
                                                  ttok)))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14235
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14206 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14171 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14273 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14273 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14287 =
                                               let uu____14288 =
                                                 let uu____14293 =
                                                   let uu____14294 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14294
                                                    in
                                                 (uu____14293,
                                                   (Some "kinding"),
                                                   (Some
                                                      (Prims.strcat
                                                         "pre_kinding_" ttok)))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14288
                                                in
                                             [uu____14287]
                                           else []  in
                                         let uu____14298 =
                                           let uu____14300 =
                                             let uu____14302 =
                                               let uu____14303 =
                                                 let uu____14308 =
                                                   let uu____14309 =
                                                     let uu____14315 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14315)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14309
                                                    in
                                                 (uu____14308, None,
                                                   (Some
                                                      (Prims.strcat
                                                         "kinding_" ttok)))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14303
                                                in
                                             [uu____14302]  in
                                           FStar_List.append karr uu____14300
                                            in
                                         FStar_List.append decls1 uu____14298
                                      in
                                   let aux =
                                     let uu____14325 =
                                       let uu____14327 =
                                         inversion_axioms tapp vars  in
                                       let uu____14329 =
                                         let uu____14331 =
                                           pretype_axiom tapp vars  in
                                         [uu____14331]  in
                                       FStar_List.append uu____14327
                                         uu____14329
                                        in
                                     FStar_List.append kindingAx uu____14325
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14336,uu____14337,uu____14338,uu____14339,uu____14340,uu____14341)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14348,t,uu____14350,n_tps,quals,uu____14353) ->
          let uu____14358 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14358 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14369 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14369 with
                | (formals,t_res) ->
                    let uu____14391 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14391 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14400 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14400 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14438 =
                                            mk_term_projector_name d x  in
                                          (uu____14438,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14440 =
                                  let uu____14450 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14450, true)
                                   in
                                FStar_All.pipe_right uu____14440
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
                              let uu____14472 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14472 with
                               | (tok_typing,decls3) ->
                                   let uu____14479 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14479 with
                                    | (vars',guards',env'',decls_formals,uu____14494)
                                        ->
                                        let uu____14501 =
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
                                        (match uu____14501 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14520 ->
                                                   let uu____14524 =
                                                     let uu____14525 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14525
                                                      in
                                                   [uu____14524]
                                                in
                                             let encode_elim uu____14532 =
                                               let uu____14533 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14533 with
                                               | (head1,args) ->
                                                   let uu____14562 =
                                                     let uu____14563 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14563.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14562 with
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
                                                        let uu____14581 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14581
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
                                                                 | uu____14607
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
                                                                    let uu____14615
                                                                    =
                                                                    let uu____14616
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14616
                                                                     in
                                                                    if
                                                                    uu____14615
                                                                    then
                                                                    let uu____14623
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14623]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14625
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14638
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14638
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14660
                                                                    =
                                                                    let uu____14664
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14664
                                                                     in
                                                                    (match uu____14660
                                                                    with
                                                                    | 
                                                                    (uu____14671,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14677
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14677
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14679
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14679
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
                                                             (match uu____14625
                                                              with
                                                              | (uu____14687,arg_vars,elim_eqns_or_guards,uu____14690)
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
                                                                    let uu____14709
                                                                    =
                                                                    let uu____14714
                                                                    =
                                                                    let uu____14715
                                                                    =
                                                                    let uu____14721
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14728
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14731)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14728
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14721,
                                                                    uu____14727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14715
                                                                     in
                                                                    (uu____14714,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14709
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14745
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14745,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14752
                                                                    =
                                                                    let uu____14753
                                                                    =
                                                                    let uu____14759
                                                                    =
                                                                    let uu____14762
                                                                    =
                                                                    let uu____14764
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14764]
                                                                     in
                                                                    [uu____14762]
                                                                     in
                                                                    let uu____14767
                                                                    =
                                                                    let uu____14768
                                                                    =
                                                                    let uu____14771
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14772
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14771,
                                                                    uu____14772)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14768
                                                                     in
                                                                    (uu____14759,
                                                                    [x],
                                                                    uu____14767)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14753
                                                                     in
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    Some
                                                                    uu____14784
                                                                     in
                                                                    (uu____14752,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14782)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14747
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14790
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
                                                                    (let uu____14805
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14806
                                                                    dapp1  in
                                                                    [uu____14805])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14790
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14810
                                                                    =
                                                                    let uu____14815
                                                                    =
                                                                    let uu____14816
                                                                    =
                                                                    let uu____14822
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14829
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14832)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14829
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14822,
                                                                    uu____14828)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14816
                                                                     in
                                                                    (uu____14815,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14810)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14843 ->
                                                        ((let uu____14845 =
                                                            let uu____14846 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14847 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14846
                                                              uu____14847
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14845);
                                                         ([], [])))
                                                in
                                             let uu____14850 = encode_elim ()
                                                in
                                             (match uu____14850 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14862 =
                                                      let uu____14864 =
                                                        let uu____14866 =
                                                          let uu____14868 =
                                                            let uu____14870 =
                                                              let uu____14871
                                                                =
                                                                let uu____14877
                                                                  =
                                                                  let uu____14879
                                                                    =
                                                                    let uu____14880
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14880
                                                                     in
                                                                  Some
                                                                    uu____14879
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14877)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14871
                                                               in
                                                            [uu____14870]  in
                                                          let uu____14883 =
                                                            let uu____14885 =
                                                              let uu____14887
                                                                =
                                                                let uu____14889
                                                                  =
                                                                  let uu____14891
                                                                    =
                                                                    let uu____14893
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    let uu____14896
                                                                    =
                                                                    let uu____14901
                                                                    =
                                                                    let uu____14902
                                                                    =
                                                                    let uu____14908
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14908)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14902
                                                                     in
                                                                    (uu____14901,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14896
                                                                     in
                                                                    let uu____14916
                                                                    =
                                                                    let uu____14918
                                                                    =
                                                                    let uu____14919
                                                                    =
                                                                    let uu____14924
                                                                    =
                                                                    let uu____14925
                                                                    =
                                                                    let uu____14931
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14931,
                                                                    uu____14937)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14925
                                                                     in
                                                                    (uu____14924,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14919
                                                                     in
                                                                    [uu____14918]
                                                                     in
                                                                    uu____14895
                                                                    ::
                                                                    uu____14916
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))))
                                                                    ::
                                                                    uu____14893
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14891
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14889
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14887
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14885
                                                             in
                                                          FStar_List.append
                                                            uu____14868
                                                            uu____14883
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14866
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14864
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14862
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
           (fun uu____14960  ->
              fun se  ->
                match uu____14960 with
                | (g,env1) ->
                    let uu____14972 = encode_sigelt env1 se  in
                    (match uu____14972 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15008 =
        match uu____15008 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15026 ->
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
                 ((let uu____15031 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15031
                   then
                     let uu____15032 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15033 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15034 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15032 uu____15033 uu____15034
                   else ());
                  (let uu____15036 = encode_term t1 env1  in
                   match uu____15036 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15046 =
                         let uu____15050 =
                           let uu____15051 =
                             let uu____15052 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15052
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15051  in
                         new_term_constant_from_string env1 x uu____15050  in
                       (match uu____15046 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____15063 = FStar_Options.log_queries ()
                                 in
                              if uu____15063
                              then
                                let uu____15065 =
                                  let uu____15066 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15067 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15068 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15066 uu____15067 uu____15068
                                   in
                                Some uu____15065
                              else None  in
                            let ax =
                              let a_name =
                                Some (Prims.strcat "binder_" xxsym)  in
                              FStar_SMTEncoding_Term.Assume
                                (t2, a_name, a_name)
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15081,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____15090 = encode_free_var env1 fv t t_norm []  in
                 (match uu____15090 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15109 = encode_sigelt env1 se  in
                 (match uu____15109 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15119 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15119 with | (uu____15131,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15176  ->
            match uu____15176 with
            | (l,uu____15183,uu____15184) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15205  ->
            match uu____15205 with
            | (l,uu____15213,uu____15214) ->
                let uu____15219 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____15220 =
                  let uu____15222 =
                    let uu____15223 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15223  in
                  [uu____15222]  in
                uu____15219 :: uu____15220))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15234 =
      let uu____15236 =
        let uu____15237 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15237;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [uu____15236]  in
    FStar_ST.write last_env uu____15234
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15255 = FStar_ST.read last_env  in
    match uu____15255 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15261 ->
        let uu___161_15263 = e  in
        {
          bindings = (uu___161_15263.bindings);
          depth = (uu___161_15263.depth);
          tcenv;
          warn = (uu___161_15263.warn);
          cache = (uu___161_15263.cache);
          nolabels = (uu___161_15263.nolabels);
          use_zfuel_name = (uu___161_15263.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15263.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15267 = FStar_ST.read last_env  in
    match uu____15267 with
    | [] -> failwith "Empty env stack"
    | uu____15272::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15280  ->
    let uu____15281 = FStar_ST.read last_env  in
    match uu____15281 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___162_15302 = hd1  in
          {
            bindings = (uu___162_15302.bindings);
            depth = (uu___162_15302.depth);
            tcenv = (uu___162_15302.tcenv);
            warn = (uu___162_15302.warn);
            cache = refs;
            nolabels = (uu___162_15302.nolabels);
            use_zfuel_name = (uu___162_15302.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15302.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15308  ->
    let uu____15309 = FStar_ST.read last_env  in
    match uu____15309 with
    | [] -> failwith "Popping an empty stack"
    | uu____15314::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15322  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15325  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15328  ->
    let uu____15329 = FStar_ST.read last_env  in
    match uu____15329 with
    | hd1::uu____15335::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15341 -> failwith "Impossible"
  
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
        let uu____15386 = FStar_Options.log_queries ()  in
        if uu____15386
        then
          let uu____15388 =
            let uu____15389 =
              let uu____15390 =
                let uu____15391 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15391 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15390  in
            FStar_SMTEncoding_Term.Caption uu____15389  in
          uu____15388 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____15398 = encode_sigelt env se  in
      match uu____15398 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15404 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15404))
  
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
      (let uu____15415 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15415
       then
         let uu____15416 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15416
       else ());
      (let env = get_env tcenv  in
       let uu____15421 =
         encode_signature
           (let uu___163_15425 = env  in
            {
              bindings = (uu___163_15425.bindings);
              depth = (uu___163_15425.depth);
              tcenv = (uu___163_15425.tcenv);
              warn = false;
              cache = (uu___163_15425.cache);
              nolabels = (uu___163_15425.nolabels);
              use_zfuel_name = (uu___163_15425.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15425.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15421 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15437 = FStar_Options.log_queries ()  in
             if uu____15437
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___164_15442 = env1  in
               {
                 bindings = (uu___164_15442.bindings);
                 depth = (uu___164_15442.depth);
                 tcenv = (uu___164_15442.tcenv);
                 warn = true;
                 cache = (uu___164_15442.cache);
                 nolabels = (uu___164_15442.nolabels);
                 use_zfuel_name = (uu___164_15442.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15442.encode_non_total_function_typ)
               });
            (let uu____15444 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15444
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
        (let uu____15479 =
           let uu____15480 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15480.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15479);
        (let env = get_env tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15488 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15509 = aux rest  in
                 (match uu____15509 with
                  | (out,rest1) ->
                      let t =
                        let uu____15527 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____15527 with
                        | Some uu____15531 ->
                            let uu____15532 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____15532
                              x.FStar_Syntax_Syntax.sort
                        | uu____15533 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____15536 =
                        let uu____15538 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15539 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15539.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15539.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____15538 :: out  in
                      (uu____15536, rest1))
             | uu____15542 -> ([], bindings1)  in
           let uu____15546 = aux bindings  in
           match uu____15546 with
           | (closing,bindings1) ->
               let uu____15560 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____15560, bindings1)
            in
         match uu____15488 with
         | (q1,bindings1) ->
             let uu____15573 =
               let uu____15576 =
                 FStar_List.filter
                   (fun uu___134_15578  ->
                      match uu___134_15578 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15579 ->
                          false
                      | uu____15583 -> true) bindings1
                  in
               encode_env_bindings env uu____15576  in
             (match uu____15573 with
              | (env_decls,env1) ->
                  ((let uu____15594 =
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
                    if uu____15594
                    then
                      let uu____15595 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15595
                    else ());
                   (let uu____15597 = encode_formula q1 env1  in
                    match uu____15597 with
                    | (phi,qdecls) ->
                        let uu____15609 =
                          let uu____15612 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15612 phi
                           in
                        (match uu____15609 with
                         | (labels,phi1) ->
                             let uu____15622 = encode_labels labels  in
                             (match uu____15622 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15643 =
                                      let uu____15648 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15649 =
                                        let uu____15651 =
                                          varops.mk_unique "@query"  in
                                        Some uu____15651  in
                                      (uu____15648, (Some "query"),
                                        uu____15649)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15643
                                     in
                                  let suffix =
                                    let uu____15656 =
                                      let uu____15658 =
                                        let uu____15660 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15660
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15658
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15656
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15673 = encode_formula q env  in
       match uu____15673 with
       | (f,uu____15677) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15679) -> true
             | uu____15682 -> false)))
  