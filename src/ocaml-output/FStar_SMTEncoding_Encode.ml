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
      let uu____1718 = FStar_Syntax_Syntax.null_binder t  in [uu____1718]  in
    let uu____1719 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____1717 uu____1719 None
  
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
                    let uu____1746 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1746
                | s ->
                    let uu____1749 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1749) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1761  ->
    match uu___118_1761 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1762 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1790;
                       FStar_SMTEncoding_Term.rng = uu____1791;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1805) ->
              let uu____1810 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1820 -> false) args vars)
                 in
              if uu____1810 then tok_of_name env f else None
          | (uu____1823,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1  in
              let uu____1826 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1828 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1828))
                 in
              if uu____1826 then Some t1 else None
          | uu____1831 -> None  in
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
      (let uu____1846 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____1846
       then
         let uu____1847 = FStar_Syntax_Print.term_to_string tm  in
         let uu____1848 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1847 uu____1848
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
    | uu____1930 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1933  ->
    match uu___119_1933 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1935 =
          let uu____1939 =
            let uu____1941 =
              let uu____1942 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____1942  in
            [uu____1941]  in
          ("FStar.Char.Char", uu____1939)  in
        FStar_SMTEncoding_Util.mkApp uu____1935
    | FStar_Const.Const_int (i,None ) ->
        let uu____1950 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____1950
    | FStar_Const.Const_int (i,Some uu____1952) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1961) ->
        let uu____1964 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____1964
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1968 =
          let uu____1969 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____1969  in
        failwith uu____1968
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1988 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1996 ->
            let uu____2001 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2001
        | uu____2002 ->
            if norm1
            then let uu____2003 = whnf env t1  in aux false uu____2003
            else
              (let uu____2005 =
                 let uu____2006 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2007 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2006 uu____2007
                  in
               failwith uu____2005)
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
    | uu____2028 ->
        let uu____2029 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2029)
  
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
        (let uu____2172 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____2172
         then
           let uu____2173 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2173
         else ());
        (let uu____2175 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2211  ->
                   fun b  ->
                     match uu____2211 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2254 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2263 = gen_term_var env1 x  in
                           match uu____2263 with
                           | (xxsym,xx,env') ->
                               let uu____2277 =
                                 let uu____2280 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2280 env1 xx
                                  in
                               (match uu____2277 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2254 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2175 with
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
          let uu____2368 = encode_term t env  in
          match uu____2368 with
          | (t1,decls) ->
              let uu____2375 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2375, decls)

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
          let uu____2383 = encode_term t env  in
          match uu____2383 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2392 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2392, decls)
               | Some f ->
                   let uu____2394 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2394, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2401 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2401
       then
         let uu____2402 = FStar_Syntax_Print.tag_of_term t  in
         let uu____2403 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____2404 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2402 uu____2403
           uu____2404
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2409 =
             let uu____2410 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2411 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2412 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2413 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2410
               uu____2411 uu____2412 uu____2413
              in
           failwith uu____2409
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2417 =
             let uu____2418 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2418
              in
           failwith uu____2417
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2423) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2453) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2462 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____2462, [])
       | FStar_Syntax_Syntax.Tm_type uu____2468 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2471) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2477 = encode_const c  in (uu____2477, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2491 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2491 with
            | (binders1,res) ->
                let uu____2498 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2498
                then
                  let uu____2501 = encode_binders None binders1 env  in
                  (match uu____2501 with
                   | (vars,guards,env',decls,uu____2516) ->
                       let fsym =
                         let uu____2526 = varops.fresh "f"  in
                         (uu____2526, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2529 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2533 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2533.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2533.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2533.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2533.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2533.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2533.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2533.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2533.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2533.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2533.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2533.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2533.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2533.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2533.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2533.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2533.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2533.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2533.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2533.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2533.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2533.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2533.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2533.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____2529 with
                        | (pre_opt,res_t) ->
                            let uu____2540 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2540 with
                             | (res_pred,decls') ->
                                 let uu____2547 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2554 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____2554, [])
                                   | Some pre ->
                                       let uu____2557 =
                                         encode_formula pre env'  in
                                       (match uu____2557 with
                                        | (guard,decls0) ->
                                            let uu____2565 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____2565, decls0))
                                    in
                                 (match uu____2547 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2573 =
                                          let uu____2579 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____2579)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2573
                                         in
                                      let cvars =
                                        let uu____2589 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____2589
                                          (FStar_List.filter
                                             (fun uu____2595  ->
                                                match uu____2595 with
                                                | (x,uu____2599) ->
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
                                      let uu____2610 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2610 with
                                       | Some (t',sorts,uu____2626) ->
                                           let uu____2636 =
                                             let uu____2637 =
                                               let uu____2641 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               (t', uu____2641)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2637
                                              in
                                           (uu____2636, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2657 =
                                               let uu____2658 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2658
                                                in
                                             varops.mk_unique uu____2657  in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2665 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2665
                                             then
                                               let uu____2667 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____2667
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____2673 =
                                               let uu____2677 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____2677)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2673
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
                                             let uu____2685 =
                                               let uu____2689 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____2689, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2685
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
                                             let uu____2702 =
                                               let uu____2706 =
                                                 let uu____2707 =
                                                   let uu____2713 =
                                                     let uu____2714 =
                                                       let uu____2717 =
                                                         let uu____2718 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2718
                                                          in
                                                       (f_has_t, uu____2717)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2714
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2713)
                                                    in
                                                 mkForall_fuel uu____2707  in
                                               (uu____2706,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2702
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____2731 =
                                               let uu____2735 =
                                                 let uu____2736 =
                                                   let uu____2742 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2742)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2736
                                                  in
                                               (uu____2735, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2731
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
                     let uu____2773 =
                       let uu____2777 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____2777, (Some "Typing for non-total arrows"),
                         a_name)
                        in
                     FStar_SMTEncoding_Term.Assume uu____2773  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____2786 =
                       let uu____2790 =
                         let uu____2791 =
                           let uu____2797 =
                             let uu____2798 =
                               let uu____2801 =
                                 let uu____2802 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2802
                                  in
                               (f_has_t, uu____2801)  in
                             FStar_SMTEncoding_Util.mkImp uu____2798  in
                           ([[f_has_t]], [fsym], uu____2797)  in
                         mkForall_fuel uu____2791  in
                       (uu____2790, (Some a_name), a_name)  in
                     FStar_SMTEncoding_Term.Assume uu____2786  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2816 ->
           let uu____2821 =
             let uu____2824 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2824 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2829;
                 FStar_Syntax_Syntax.pos = uu____2830;
                 FStar_Syntax_Syntax.vars = uu____2831;_} ->
                 let uu____2838 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2838 with
                  | (b,f1) ->
                      let uu____2852 =
                        let uu____2853 = FStar_List.hd b  in
                        Prims.fst uu____2853  in
                      (uu____2852, f1))
             | uu____2858 -> failwith "impossible"  in
           (match uu____2821 with
            | (x,f) ->
                let uu____2865 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2865 with
                 | (base_t,decls) ->
                     let uu____2872 = gen_term_var env x  in
                     (match uu____2872 with
                      | (x1,xtm,env') ->
                          let uu____2881 = encode_formula f env'  in
                          (match uu____2881 with
                           | (refinement,decls') ->
                               let uu____2888 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2888 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2896 =
                                        let uu____2899 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t
                                           in
                                        (uu____2899, refinement)  in
                                      FStar_SMTEncoding_Util.mkAnd uu____2896
                                       in
                                    let cvars =
                                      let uu____2904 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right uu____2904
                                        (FStar_List.filter
                                           (fun uu____2910  ->
                                              match uu____2910 with
                                              | (y,uu____2914) ->
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
                                    let uu____2933 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2933 with
                                     | Some (t1,uu____2948,uu____2949) ->
                                         let uu____2959 =
                                           let uu____2960 =
                                             let uu____2964 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (t1, uu____2964)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2960
                                            in
                                         (uu____2959, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2980 =
                                             let uu____2981 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash
                                                in
                                             Prims.strcat "Tm_refine_"
                                               uu____2981
                                              in
                                           varops.mk_unique uu____2980  in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars  in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____2990 =
                                             let uu____2994 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars
                                                in
                                             (tsym, uu____2994)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2990
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
                                           let uu____3004 =
                                             let uu____3008 =
                                               let uu____3009 =
                                                 let uu____3015 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____3015)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3009
                                                in
                                             (uu____3008,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3004
                                            in
                                         let t_kinding =
                                           let uu____3025 =
                                             let uu____3029 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind)
                                                in
                                             (uu____3029,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3025
                                            in
                                         let t_interp =
                                           let uu____3039 =
                                             let uu____3043 =
                                               let uu____3044 =
                                                 let uu____3050 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3050)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3044
                                                in
                                             let uu____3062 =
                                               let uu____3064 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3064  in
                                             (uu____3043, uu____3062,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3039
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
             let uu____3092 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3092  in
           let uu____3096 = encode_term_pred None k env ttm  in
           (match uu____3096 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3104 =
                    let uu____3108 =
                      let uu____3109 =
                        let uu____3110 =
                          let uu____3111 = FStar_Unionfind.uvar_id uv  in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3111
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____3110  in
                      varops.mk_unique uu____3109  in
                    (t_has_k, (Some "Uvar typing"), uu____3108)  in
                  FStar_SMTEncoding_Term.Assume uu____3104  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3117 ->
           let uu____3127 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3127 with
            | (head1,args_e) ->
                let uu____3155 =
                  let uu____3163 =
                    let uu____3164 = FStar_Syntax_Subst.compress head1  in
                    uu____3164.FStar_Syntax_Syntax.n  in
                  (uu____3163, args_e)  in
                (match uu____3155 with
                 | (uu____3174,uu____3175) when head_redex env head1 ->
                     let uu____3186 = whnf env t  in
                     encode_term uu____3186 env
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
                     let uu____3260 = encode_term v1 env  in
                     (match uu____3260 with
                      | (v11,decls1) ->
                          let uu____3267 = encode_term v2 env  in
                          (match uu____3267 with
                           | (v21,decls2) ->
                               let uu____3274 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3274,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3276) ->
                     let e0 =
                       let uu____3290 =
                         let uu____3293 =
                           let uu____3294 =
                             let uu____3304 =
                               let uu____3310 = FStar_List.hd args_e  in
                               [uu____3310]  in
                             (head1, uu____3304)  in
                           FStar_Syntax_Syntax.Tm_app uu____3294  in
                         FStar_Syntax_Syntax.mk uu____3293  in
                       uu____3290 None head1.FStar_Syntax_Syntax.pos  in
                     ((let uu____3343 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____3343
                       then
                         let uu____3344 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3344
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
                       (let uu____3348 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        if uu____3348
                        then
                          let uu____3349 =
                            FStar_Syntax_Print.term_to_string e01  in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3349
                        else ());
                       (let e02 =
                          let uu____3352 =
                            let uu____3353 =
                              let uu____3354 =
                                FStar_Syntax_Subst.compress e01  in
                              uu____3354.FStar_Syntax_Syntax.n  in
                            match uu____3353 with
                            | FStar_Syntax_Syntax.Tm_app uu____3357 -> false
                            | uu____3367 -> true  in
                          if uu____3352
                          then e01
                          else
                            (let uu____3369 =
                               FStar_Syntax_Util.head_and_args e01  in
                             match uu____3369 with
                             | (head2,args) ->
                                 let uu____3395 =
                                   let uu____3396 =
                                     let uu____3397 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____3397.FStar_Syntax_Syntax.n  in
                                   match uu____3396 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3400 -> false  in
                                 if uu____3395
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3416 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01)
                           in
                        let e =
                          match args_e with
                          | uu____3424::[] -> e02
                          | uu____3437 ->
                              let uu____3443 =
                                let uu____3446 =
                                  let uu____3447 =
                                    let uu____3457 = FStar_List.tl args_e  in
                                    (e02, uu____3457)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3447  in
                                FStar_Syntax_Syntax.mk uu____3446  in
                              uu____3443 None t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3480),(arg,uu____3482)::[]) -> encode_term arg env
                 | uu____3500 ->
                     let uu____3508 = encode_args args_e env  in
                     (match uu____3508 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3541 = encode_term head1 env  in
                            match uu____3541 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3580 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3580 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3622  ->
                                                 fun uu____3623  ->
                                                   match (uu____3622,
                                                           uu____3623)
                                                   with
                                                   | ((bv,uu____3637),
                                                      (a,uu____3639)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3653 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3653
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3658 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3658 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3668 =
                                                   let uu____3672 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3677 =
                                                     let uu____3678 =
                                                       let uu____3679 =
                                                         let uu____3680 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____3680
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3679
                                                        in
                                                     varops.mk_unique
                                                       uu____3678
                                                      in
                                                   (uu____3672,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3677)
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3668
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3697 = lookup_free_var_sym env fv  in
                            match uu____3697 with
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
                                let uu____3735 =
                                  let uu____3736 =
                                    let uu____3739 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____3739 Prims.fst
                                     in
                                  FStar_All.pipe_right uu____3736 Prims.snd
                                   in
                                Some uu____3735
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3758,(FStar_Util.Inl t1,uu____3760),uu____3761)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3799,(FStar_Util.Inr c,uu____3801),uu____3802)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3840 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3860 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3860
                                  in
                               let uu____3861 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____3861 with
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
                                     | uu____3886 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3931 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3931 with
            | (bs1,body1,opening) ->
                let fallback uu____3946 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____3951 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____3951, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3962 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1  in
                      Prims.op_Negation uu____3962
                  | FStar_Util.Inr (eff,uu____3964) ->
                      let uu____3970 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____3970 Prims.op_Negation
                   in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2  in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4015 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4016 = env1.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4016.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4016.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4016.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4016.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4016.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4016.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4016.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4016.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4016.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4016.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4016.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4016.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4016.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4016.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4016.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4016.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4016.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4016.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4016.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4016.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4016.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4016.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4016.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4015 FStar_Syntax_Syntax.U_unknown
                           in
                        let uu____4017 =
                          let uu____4018 = FStar_Syntax_Syntax.mk_Total typ
                             in
                          FStar_Syntax_Util.lcomp_of_comp uu____4018  in
                        FStar_Util.Inl uu____4017
                    | FStar_Util.Inr (eff_name,uu____4025) -> c  in
                  (c1, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4056 =
                        let uu____4057 = lc1.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____4057  in
                      FStar_All.pipe_right uu____4056
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4069 =
                        let uu____4070 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____4070 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4078 =
                          let uu____4079 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____4079  in
                        FStar_All.pipe_right uu____4078
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4083 =
                             let uu____4084 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____4084  in
                           FStar_All.pipe_right uu____4083
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____4095 =
                         let uu____4096 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4096
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4095);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc  in
                     let uu____4111 =
                       (is_impure lc1) &&
                         (let uu____4112 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1
                             in
                          Prims.op_Negation uu____4112)
                        in
                     if uu____4111
                     then fallback ()
                     else
                       (let uu____4116 = encode_binders None bs1 env  in
                        match uu____4116 with
                        | (vars,guards,envbody,decls,uu____4131) ->
                            let uu____4138 =
                              let uu____4146 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1
                                 in
                              if uu____4146
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1)  in
                            (match uu____4138 with
                             | (lc2,body2) ->
                                 let uu____4171 = encode_term body2 envbody
                                    in
                                 (match uu____4171 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4179 =
                                          let uu____4185 =
                                            let uu____4186 =
                                              let uu____4189 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____4189, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4186
                                             in
                                          ([], vars, uu____4185)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4179
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
                                      let uu____4200 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____4200 with
                                       | Some (t1,uu____4215,uu____4216) ->
                                           let uu____4226 =
                                             let uu____4227 =
                                               let uu____4231 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (t1, uu____4231)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4227
                                              in
                                           (uu____4226, [])
                                       | None  ->
                                           let uu____4242 =
                                             is_eta env vars body3  in
                                           (match uu____4242 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars
                                                   in
                                                let fsym =
                                                  let uu____4253 =
                                                    let uu____4254 =
                                                      FStar_Util.digest_of_string
                                                        tkey_hash
                                                       in
                                                    Prims.strcat "Tm_abs_"
                                                      uu____4254
                                                     in
                                                  varops.mk_unique uu____4253
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  let uu____4259 =
                                                    let uu____4263 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars
                                                       in
                                                    (fsym, uu____4263)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4259
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  let uu____4271 =
                                                    codomain_eff lc2  in
                                                  match uu____4271 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c
                                                         in
                                                      let uu____4278 =
                                                        encode_term_pred None
                                                          tfun env f
                                                         in
                                                      (match uu____4278 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym
                                                              in
                                                           let uu____4285 =
                                                             let uu____4287 =
                                                               let uu____4288
                                                                 =
                                                                 let uu____4292
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                    in
                                                                 (uu____4292,
                                                                   (Some
                                                                    a_name),
                                                                   a_name)
                                                                  in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4288
                                                                in
                                                             [uu____4287]  in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4285)
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____4300 =
                                                    let uu____4304 =
                                                      let uu____4305 =
                                                        let uu____4311 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4311)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4305
                                                       in
                                                    (uu____4304,
                                                      (Some a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4300
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
           ((uu____4329,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4330;
                          FStar_Syntax_Syntax.lbunivs = uu____4331;
                          FStar_Syntax_Syntax.lbtyp = uu____4332;
                          FStar_Syntax_Syntax.lbeff = uu____4333;
                          FStar_Syntax_Syntax.lbdef = uu____4334;_}::uu____4335),uu____4336)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4354;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4356;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4372 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4385 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4385, [decl_e])))
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
              let uu____4427 = encode_term e1 env  in
              match uu____4427 with
              | (ee1,decls1) ->
                  let uu____4434 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4434 with
                   | (xs,e21) ->
                       let uu____4448 = FStar_List.hd xs  in
                       (match uu____4448 with
                        | (x1,uu____4456) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4458 = encode_body e21 env'  in
                            (match uu____4458 with
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
            let uu____4480 =
              let uu____4484 =
                let uu____4485 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4485  in
              gen_term_var env uu____4484  in
            match uu____4480 with
            | (scrsym,scr',env1) ->
                let uu____4499 = encode_term e env1  in
                (match uu____4499 with
                 | (scr,decls) ->
                     let uu____4506 =
                       let encode_branch b uu____4522 =
                         match uu____4522 with
                         | (else_case,decls1) ->
                             let uu____4533 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4533 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p  in
                                  FStar_List.fold_right
                                    (fun uu____4563  ->
                                       fun uu____4564  ->
                                         match (uu____4563, uu____4564) with
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
                                                       fun uu____4601  ->
                                                         match uu____4601
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1)
                                                in
                                             let uu____4606 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4621 =
                                                     encode_term w1 env2  in
                                                   (match uu____4621 with
                                                    | (w2,decls21) ->
                                                        let uu____4629 =
                                                          let uu____4630 =
                                                            let uu____4633 =
                                                              let uu____4634
                                                                =
                                                                let uu____4637
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4637)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4634
                                                               in
                                                            (guard,
                                                              uu____4633)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4630
                                                           in
                                                        (uu____4629, decls21))
                                                in
                                             (match uu____4606 with
                                              | (guard1,decls21) ->
                                                  let uu____4645 =
                                                    encode_br br env2  in
                                                  (match uu____4645 with
                                                   | (br1,decls3) ->
                                                       let uu____4653 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4653,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4506 with
                      | (match_tm,decls1) ->
                          let uu____4665 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4665, decls1)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4696 ->
          let uu____4697 = encode_one_pat env pat  in [uu____4697]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4709 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4709
       then
         let uu____4710 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4710
       else ());
      (let uu____4712 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4712 with
       | (vars,pat_term) ->
           let uu____4722 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4745  ->
                     fun v1  ->
                       match uu____4745 with
                       | (env1,vars1) ->
                           let uu____4773 = gen_term_var env1 v1  in
                           (match uu____4773 with
                            | (xx,uu____4785,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4722 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4832 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4840 =
                        let uu____4843 = encode_const c  in
                        (scrutinee, uu____4843)  in
                      FStar_SMTEncoding_Util.mkEq uu____4840
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4862 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____4862 with
                        | (uu____4866,uu____4867::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4869 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4890  ->
                                  match uu____4890 with
                                  | (arg,uu____4896) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4906 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4906))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4925 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4940 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4955 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4977  ->
                                  match uu____4977 with
                                  | (arg,uu____4986) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4996 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____4996))
                         in
                      FStar_All.pipe_right uu____4955 FStar_List.flatten
                   in
                let pat_term1 uu____5012 = encode_term pat_term env1  in
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
      let uu____5019 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5034  ->
                fun uu____5035  ->
                  match (uu____5034, uu____5035) with
                  | ((tms,decls),(t,uu____5055)) ->
                      let uu____5066 = encode_term t env  in
                      (match uu____5066 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5019 with | (l1,decls) -> ((FStar_List.rev l1), decls)

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
            let uu____5104 = FStar_Syntax_Util.list_elements e  in
            match uu____5104 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____5122 =
              let uu____5132 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____5132 FStar_Syntax_Util.head_and_args
               in
            match uu____5122 with
            | (head1,args) ->
                let uu____5163 =
                  let uu____5171 =
                    let uu____5172 = FStar_Syntax_Util.un_uinst head1  in
                    uu____5172.FStar_Syntax_Syntax.n  in
                  (uu____5171, args)  in
                (match uu____5163 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5186,uu____5187)::(e,uu____5189)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5220)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5241 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____5274 =
                let uu____5284 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____5284
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____5274 with
              | (head1,args) ->
                  let uu____5313 =
                    let uu____5321 =
                      let uu____5322 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5322.FStar_Syntax_Syntax.n  in
                    (uu____5321, args)  in
                  (match uu____5313 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5335)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5355 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5373 = smt_pat_or t1  in
                (match uu____5373 with
                 | Some e ->
                     let uu____5389 = list_elements1 e  in
                     FStar_All.pipe_right uu____5389
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5406 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5406
                               (FStar_List.map one_pat)))
                 | uu____5420 ->
                     let uu____5424 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5424])
            | uu____5455 ->
                let uu____5457 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5457]
             in
          let uu____5488 =
            let uu____5504 =
              let uu____5505 = FStar_Syntax_Subst.compress t  in
              uu____5505.FStar_Syntax_Syntax.n  in
            match uu____5504 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5535 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5535 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5570;
                            FStar_Syntax_Syntax.effect_name = uu____5571;
                            FStar_Syntax_Syntax.result_typ = uu____5572;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5574)::(post,uu____5576)::(pats,uu____5578)::[];
                            FStar_Syntax_Syntax.flags = uu____5579;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5613 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5613)
                      | uu____5632 -> failwith "impos"))
            | uu____5648 -> failwith "Impos"  in
          match uu____5488 with
          | (binders,pre,post,patterns) ->
              let uu____5692 = encode_binders None binders env  in
              (match uu____5692 with
               | (vars,guards,env1,decls,uu____5707) ->
                   let uu____5714 =
                     let uu____5721 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5752 =
                                 let uu____5757 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5773  ->
                                           match uu____5773 with
                                           | (t1,uu____5780) ->
                                               encode_term t1
                                                 (let uu___146_5783 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___146_5783.bindings);
                                                    depth =
                                                      (uu___146_5783.depth);
                                                    tcenv =
                                                      (uu___146_5783.tcenv);
                                                    warn =
                                                      (uu___146_5783.warn);
                                                    cache =
                                                      (uu___146_5783.cache);
                                                    nolabels =
                                                      (uu___146_5783.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5783.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5757
                                   FStar_List.unzip
                                  in
                               match uu____5752 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5721 FStar_List.unzip  in
                   (match uu____5714 with
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
                                           let uu____5847 =
                                             let uu____5848 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5848 e
                                              in
                                           uu____5847 :: p))
                               | uu____5849 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5878 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5878 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5886 =
                                           let uu____5887 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5887 tl1
                                            in
                                         aux uu____5886 vars2
                                     | uu____5888 -> pats  in
                                   let uu____5892 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5892 vars)
                           in
                        let env2 =
                          let uu___147_5894 = env1  in
                          {
                            bindings = (uu___147_5894.bindings);
                            depth = (uu___147_5894.depth);
                            tcenv = (uu___147_5894.tcenv);
                            warn = (uu___147_5894.warn);
                            cache = (uu___147_5894.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5894.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5894.encode_non_total_function_typ)
                          }  in
                        let uu____5895 =
                          let uu____5898 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5898 env2  in
                        (match uu____5895 with
                         | (pre1,decls'') ->
                             let uu____5903 =
                               let uu____5906 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5906 env2  in
                             (match uu____5903 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5913 =
                                    let uu____5914 =
                                      let uu____5920 =
                                        let uu____5921 =
                                          let uu____5924 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5924, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5921
                                         in
                                      (pats1, vars, uu____5920)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5914
                                     in
                                  (uu____5913, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5937 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5937
        then
          let uu____5938 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5939 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5938 uu____5939
        else ()  in
      let enc f r l =
        let uu____5966 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5979 = encode_term (Prims.fst x) env  in
                 match uu____5979 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5966 with
        | (decls,args) ->
            let uu____5996 =
              let uu___148_5997 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_5997.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_5997.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____5996, decls)
         in
      let const_op f r uu____6016 = let uu____6019 = f r  in (uu____6019, [])
         in
      let un_op f l =
        let uu____6035 = FStar_List.hd l  in FStar_All.pipe_left f uu____6035
         in
      let bin_op f uu___120_6048 =
        match uu___120_6048 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6056 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6083 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6092  ->
                 match uu____6092 with
                 | (t,uu____6100) ->
                     let uu____6101 = encode_formula t env  in
                     (match uu____6101 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6083 with
        | (decls,phis) ->
            let uu____6118 =
              let uu___149_6119 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6119.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6119.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6118, decls)
         in
      let eq_op r uu___121_6135 =
        match uu___121_6135 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6195 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6195 r [e1; e2]
        | l ->
            let uu____6215 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6215 r l
         in
      let mk_imp1 r uu___122_6234 =
        match uu___122_6234 with
        | (lhs,uu____6238)::(rhs,uu____6240)::[] ->
            let uu____6261 = encode_formula rhs env  in
            (match uu____6261 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6270) ->
                      (l1, decls1)
                  | uu____6273 ->
                      let uu____6274 = encode_formula lhs env  in
                      (match uu____6274 with
                       | (l2,decls2) ->
                           let uu____6281 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6281, (FStar_List.append decls1 decls2)))))
        | uu____6283 -> failwith "impossible"  in
      let mk_ite r uu___123_6298 =
        match uu___123_6298 with
        | (guard,uu____6302)::(_then,uu____6304)::(_else,uu____6306)::[] ->
            let uu____6335 = encode_formula guard env  in
            (match uu____6335 with
             | (g,decls1) ->
                 let uu____6342 = encode_formula _then env  in
                 (match uu____6342 with
                  | (t,decls2) ->
                      let uu____6349 = encode_formula _else env  in
                      (match uu____6349 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6358 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6377 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6377  in
      let connectives =
        let uu____6389 =
          let uu____6398 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6398)  in
        let uu____6411 =
          let uu____6421 =
            let uu____6430 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6430)  in
          let uu____6443 =
            let uu____6453 =
              let uu____6463 =
                let uu____6472 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6472)  in
              let uu____6485 =
                let uu____6495 =
                  let uu____6505 =
                    let uu____6514 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6514)  in
                  [uu____6505;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6495  in
              uu____6463 :: uu____6485  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6453  in
          uu____6421 :: uu____6443  in
        uu____6389 :: uu____6411  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6676 = encode_formula phi' env  in
            (match uu____6676 with
             | (phi2,decls) ->
                 let uu____6683 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6683, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6684 ->
            let uu____6689 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6689 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6718 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6718 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6726;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6728;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6744 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6744 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6776::(x,uu____6778)::(t,uu____6780)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6814 = encode_term x env  in
                 (match uu____6814 with
                  | (x1,decls) ->
                      let uu____6821 = encode_term t env  in
                      (match uu____6821 with
                       | (t1,decls') ->
                           let uu____6828 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6828, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6832)::(msg,uu____6834)::(phi2,uu____6836)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6870 =
                   let uu____6873 =
                     let uu____6874 = FStar_Syntax_Subst.compress r  in
                     uu____6874.FStar_Syntax_Syntax.n  in
                   let uu____6877 =
                     let uu____6878 = FStar_Syntax_Subst.compress msg  in
                     uu____6878.FStar_Syntax_Syntax.n  in
                   (uu____6873, uu____6877)  in
                 (match uu____6870 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6885))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6901 -> fallback phi2)
             | uu____6904 when head_redex env head2 ->
                 let uu____6912 = whnf env phi1  in
                 encode_formula uu____6912 env
             | uu____6913 ->
                 let uu____6921 = encode_term phi1 env  in
                 (match uu____6921 with
                  | (tt,decls) ->
                      let uu____6928 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6929 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6929.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6929.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6928, decls)))
        | uu____6932 ->
            let uu____6933 = encode_term phi1 env  in
            (match uu____6933 with
             | (tt,decls) ->
                 let uu____6940 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6941 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6941.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6941.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6940, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____6968 = encode_binders None bs env1  in
        match uu____6968 with
        | (vars,guards,env2,decls,uu____6990) ->
            let uu____6997 =
              let uu____7004 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7027 =
                          let uu____7032 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7046  ->
                                    match uu____7046 with
                                    | (t,uu____7052) ->
                                        encode_term t
                                          (let uu___152_7053 = env2  in
                                           {
                                             bindings =
                                               (uu___152_7053.bindings);
                                             depth = (uu___152_7053.depth);
                                             tcenv = (uu___152_7053.tcenv);
                                             warn = (uu___152_7053.warn);
                                             cache = (uu___152_7053.cache);
                                             nolabels =
                                               (uu___152_7053.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7053.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right uu____7032 FStar_List.unzip
                           in
                        match uu____7027 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7004 FStar_List.unzip  in
            (match uu____6997 with
             | (pats,decls') ->
                 let uu____7105 = encode_formula body env2  in
                 (match uu____7105 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7124;
                             FStar_SMTEncoding_Term.rng = uu____7125;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7133 -> guards  in
                      let uu____7136 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7136, body1,
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
                (fun uu____7170  ->
                   match uu____7170 with
                   | (x,uu____7174) ->
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
               let uu____7180 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7186 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7186) uu____7180 tl1
                in
             let uu____7188 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7200  ->
                       match uu____7200 with
                       | (b,uu____7204) ->
                           let uu____7205 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7205))
                in
             (match uu____7188 with
              | None  -> ()
              | Some (x,uu____7209) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7219 =
                    let uu____7220 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7220
                     in
                  FStar_Errors.warn pos uu____7219)
          in
       let uu____7221 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7221 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7227 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7263  ->
                     match uu____7263 with
                     | (l,uu____7273) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7227 with
            | None  -> fallback phi1
            | Some (uu____7296,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7325 = encode_q_body env vars pats body  in
             match uu____7325 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7351 =
                     let uu____7357 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7357)  in
                   FStar_SMTEncoding_Term.mkForall uu____7351
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7369 = encode_q_body env vars pats body  in
             match uu____7369 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7394 =
                   let uu____7395 =
                     let uu____7401 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7401)  in
                   FStar_SMTEncoding_Term.mkExists uu____7395
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7394, decls))))

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
  let uu____7450 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7450 with
  | (asym,a) ->
      let uu____7455 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7455 with
       | (xsym,x) ->
           let uu____7460 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7460 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7490 =
                      let uu____7496 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7496, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7490  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7511 =
                      let uu____7515 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7515)  in
                    FStar_SMTEncoding_Util.mkApp uu____7511  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7523 =
                    let uu____7525 =
                      let uu____7527 =
                        let uu____7529 =
                          let uu____7530 =
                            let uu____7534 =
                              let uu____7535 =
                                let uu____7541 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7541)  in
                              FStar_SMTEncoding_Util.mkForall uu____7535  in
                            (uu____7534, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7530  in
                        let uu____7550 =
                          let uu____7552 =
                            let uu____7553 =
                              let uu____7557 =
                                let uu____7558 =
                                  let uu____7564 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7564)  in
                                FStar_SMTEncoding_Util.mkForall uu____7558
                                 in
                              (uu____7557,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7553  in
                          [uu____7552]  in
                        uu____7529 :: uu____7550  in
                      xtok_decl :: uu____7527  in
                    xname_decl :: uu____7525  in
                  (xtok1, uu____7523)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7613 =
                    let uu____7621 =
                      let uu____7627 =
                        let uu____7628 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7628
                         in
                      quant axy uu____7627  in
                    (FStar_Syntax_Const.op_Eq, uu____7621)  in
                  let uu____7634 =
                    let uu____7643 =
                      let uu____7651 =
                        let uu____7657 =
                          let uu____7658 =
                            let uu____7659 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7659  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7658
                           in
                        quant axy uu____7657  in
                      (FStar_Syntax_Const.op_notEq, uu____7651)  in
                    let uu____7665 =
                      let uu____7674 =
                        let uu____7682 =
                          let uu____7688 =
                            let uu____7689 =
                              let uu____7690 =
                                let uu____7693 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7694 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7693, uu____7694)  in
                              FStar_SMTEncoding_Util.mkLT uu____7690  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7689
                             in
                          quant xy uu____7688  in
                        (FStar_Syntax_Const.op_LT, uu____7682)  in
                      let uu____7700 =
                        let uu____7709 =
                          let uu____7717 =
                            let uu____7723 =
                              let uu____7724 =
                                let uu____7725 =
                                  let uu____7728 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7729 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7728, uu____7729)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7725  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7724
                               in
                            quant xy uu____7723  in
                          (FStar_Syntax_Const.op_LTE, uu____7717)  in
                        let uu____7735 =
                          let uu____7744 =
                            let uu____7752 =
                              let uu____7758 =
                                let uu____7759 =
                                  let uu____7760 =
                                    let uu____7763 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7764 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7763, uu____7764)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7760  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7759
                                 in
                              quant xy uu____7758  in
                            (FStar_Syntax_Const.op_GT, uu____7752)  in
                          let uu____7770 =
                            let uu____7779 =
                              let uu____7787 =
                                let uu____7793 =
                                  let uu____7794 =
                                    let uu____7795 =
                                      let uu____7798 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7799 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7798, uu____7799)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7795
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7794
                                   in
                                quant xy uu____7793  in
                              (FStar_Syntax_Const.op_GTE, uu____7787)  in
                            let uu____7805 =
                              let uu____7814 =
                                let uu____7822 =
                                  let uu____7828 =
                                    let uu____7829 =
                                      let uu____7830 =
                                        let uu____7833 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7834 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7833, uu____7834)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7830
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7829
                                     in
                                  quant xy uu____7828  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7822)
                                 in
                              let uu____7840 =
                                let uu____7849 =
                                  let uu____7857 =
                                    let uu____7863 =
                                      let uu____7864 =
                                        let uu____7865 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7865
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7864
                                       in
                                    quant qx uu____7863  in
                                  (FStar_Syntax_Const.op_Minus, uu____7857)
                                   in
                                let uu____7871 =
                                  let uu____7880 =
                                    let uu____7888 =
                                      let uu____7894 =
                                        let uu____7895 =
                                          let uu____7896 =
                                            let uu____7899 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7900 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7899, uu____7900)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7896
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7895
                                         in
                                      quant xy uu____7894  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7888)
                                     in
                                  let uu____7906 =
                                    let uu____7915 =
                                      let uu____7923 =
                                        let uu____7929 =
                                          let uu____7930 =
                                            let uu____7931 =
                                              let uu____7934 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7935 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7934, uu____7935)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7931
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7930
                                           in
                                        quant xy uu____7929  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7923)
                                       in
                                    let uu____7941 =
                                      let uu____7950 =
                                        let uu____7958 =
                                          let uu____7964 =
                                            let uu____7965 =
                                              let uu____7966 =
                                                let uu____7969 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____7970 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____7969, uu____7970)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7966
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7965
                                             in
                                          quant xy uu____7964  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7958)
                                         in
                                      let uu____7976 =
                                        let uu____7985 =
                                          let uu____7993 =
                                            let uu____7999 =
                                              let uu____8000 =
                                                let uu____8001 =
                                                  let uu____8004 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8005 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8004, uu____8005)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8001
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8000
                                               in
                                            quant xy uu____7999  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7993)
                                           in
                                        let uu____8011 =
                                          let uu____8020 =
                                            let uu____8028 =
                                              let uu____8034 =
                                                let uu____8035 =
                                                  let uu____8036 =
                                                    let uu____8039 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8040 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8039, uu____8040)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8036
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8035
                                                 in
                                              quant xy uu____8034  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8028)
                                             in
                                          let uu____8046 =
                                            let uu____8055 =
                                              let uu____8063 =
                                                let uu____8069 =
                                                  let uu____8070 =
                                                    let uu____8071 =
                                                      let uu____8074 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8075 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8074,
                                                        uu____8075)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8071
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8070
                                                   in
                                                quant xy uu____8069  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8063)
                                               in
                                            let uu____8081 =
                                              let uu____8090 =
                                                let uu____8098 =
                                                  let uu____8104 =
                                                    let uu____8105 =
                                                      let uu____8106 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8106
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8105
                                                     in
                                                  quant qx uu____8104  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8098)
                                                 in
                                              [uu____8090]  in
                                            uu____8055 :: uu____8081  in
                                          uu____8020 :: uu____8046  in
                                        uu____7985 :: uu____8011  in
                                      uu____7950 :: uu____7976  in
                                    uu____7915 :: uu____7941  in
                                  uu____7880 :: uu____7906  in
                                uu____7849 :: uu____7871  in
                              uu____7814 :: uu____7840  in
                            uu____7779 :: uu____7805  in
                          uu____7744 :: uu____7770  in
                        uu____7709 :: uu____7735  in
                      uu____7674 :: uu____7700  in
                    uu____7643 :: uu____7665  in
                  uu____7613 :: uu____7634  in
                let mk1 l v1 =
                  let uu____8234 =
                    let uu____8239 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8271  ->
                              match uu____8271 with
                              | (l',uu____8280) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8239
                      (FStar_Option.map
                         (fun uu____8313  ->
                            match uu____8313 with | (uu____8324,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8234 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8365  ->
                          match uu____8365 with
                          | (l',uu____8374) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8397 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____8397 with
      | (xxsym,xx) ->
          let uu____8402 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____8402 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               let uu____8409 =
                 let uu____8413 =
                   let uu____8414 =
                     let uu____8420 =
                       let uu____8421 =
                         let uu____8424 =
                           let uu____8425 =
                             let uu____8428 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx])
                                in
                             (tapp, uu____8428)  in
                           FStar_SMTEncoding_Util.mkEq uu____8425  in
                         (xx_has_type, uu____8424)  in
                       FStar_SMTEncoding_Util.mkImp uu____8421  in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8420)
                      in
                   FStar_SMTEncoding_Util.mkForall uu____8414  in
                 let uu____8441 =
                   let uu____8442 =
                     let uu____8443 = FStar_Util.digest_of_string tapp_hash
                        in
                     Prims.strcat "pretyping_" uu____8443  in
                   varops.mk_unique uu____8442  in
                 (uu____8413, (Some "pretyping"), uu____8441)  in
               FStar_SMTEncoding_Term.Assume uu____8409)
  
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
    let uu____8473 =
      let uu____8474 =
        let uu____8478 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8478, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8474  in
    let uu____8480 =
      let uu____8482 =
        let uu____8483 =
          let uu____8487 =
            let uu____8488 =
              let uu____8494 =
                let uu____8495 =
                  let uu____8498 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8498)  in
                FStar_SMTEncoding_Util.mkImp uu____8495  in
              ([[typing_pred]], [xx], uu____8494)  in
            mkForall_fuel uu____8488  in
          (uu____8487, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8483  in
      [uu____8482]  in
    uu____8473 :: uu____8480  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8526 =
      let uu____8527 =
        let uu____8531 =
          let uu____8532 =
            let uu____8538 =
              let uu____8541 =
                let uu____8543 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8543]  in
              [uu____8541]  in
            let uu____8546 =
              let uu____8547 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8547 tt  in
            (uu____8538, [bb], uu____8546)  in
          FStar_SMTEncoding_Util.mkForall uu____8532  in
        (uu____8531, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8527  in
    let uu____8558 =
      let uu____8560 =
        let uu____8561 =
          let uu____8565 =
            let uu____8566 =
              let uu____8572 =
                let uu____8573 =
                  let uu____8576 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8576)  in
                FStar_SMTEncoding_Util.mkImp uu____8573  in
              ([[typing_pred]], [xx], uu____8572)  in
            mkForall_fuel uu____8566  in
          (uu____8565, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8561  in
      [uu____8560]  in
    uu____8526 :: uu____8558  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8610 =
        let uu____8611 =
          let uu____8615 =
            let uu____8617 =
              let uu____8619 =
                let uu____8621 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8622 =
                  let uu____8624 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8624]  in
                uu____8621 :: uu____8622  in
              tt :: uu____8619  in
            tt :: uu____8617  in
          ("Prims.Precedes", uu____8615)  in
        FStar_SMTEncoding_Util.mkApp uu____8611  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8610  in
    let precedes_y_x =
      let uu____8627 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8627  in
    let uu____8629 =
      let uu____8630 =
        let uu____8634 =
          let uu____8635 =
            let uu____8641 =
              let uu____8644 =
                let uu____8646 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8646]  in
              [uu____8644]  in
            let uu____8649 =
              let uu____8650 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8650 tt  in
            (uu____8641, [bb], uu____8649)  in
          FStar_SMTEncoding_Util.mkForall uu____8635  in
        (uu____8634, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8630  in
    let uu____8661 =
      let uu____8663 =
        let uu____8664 =
          let uu____8668 =
            let uu____8669 =
              let uu____8675 =
                let uu____8676 =
                  let uu____8679 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8679)  in
                FStar_SMTEncoding_Util.mkImp uu____8676  in
              ([[typing_pred]], [xx], uu____8675)  in
            mkForall_fuel uu____8669  in
          (uu____8668, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8664  in
      let uu____8692 =
        let uu____8694 =
          let uu____8695 =
            let uu____8699 =
              let uu____8700 =
                let uu____8706 =
                  let uu____8707 =
                    let uu____8710 =
                      let uu____8711 =
                        let uu____8713 =
                          let uu____8715 =
                            let uu____8717 =
                              let uu____8718 =
                                let uu____8721 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8722 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8721, uu____8722)  in
                              FStar_SMTEncoding_Util.mkGT uu____8718  in
                            let uu____8723 =
                              let uu____8725 =
                                let uu____8726 =
                                  let uu____8729 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8730 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8729, uu____8730)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8726  in
                              let uu____8731 =
                                let uu____8733 =
                                  let uu____8734 =
                                    let uu____8737 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8738 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8737, uu____8738)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8734  in
                                [uu____8733]  in
                              uu____8725 :: uu____8731  in
                            uu____8717 :: uu____8723  in
                          typing_pred_y :: uu____8715  in
                        typing_pred :: uu____8713  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8711  in
                    (uu____8710, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8707  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8706)
                 in
              mkForall_fuel uu____8700  in
            (uu____8699, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Term.Assume uu____8695  in
        [uu____8694]  in
      uu____8663 :: uu____8692  in
    uu____8629 :: uu____8661  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8768 =
      let uu____8769 =
        let uu____8773 =
          let uu____8774 =
            let uu____8780 =
              let uu____8783 =
                let uu____8785 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8785]  in
              [uu____8783]  in
            let uu____8788 =
              let uu____8789 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8789 tt  in
            (uu____8780, [bb], uu____8788)  in
          FStar_SMTEncoding_Util.mkForall uu____8774  in
        (uu____8773, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8769  in
    let uu____8800 =
      let uu____8802 =
        let uu____8803 =
          let uu____8807 =
            let uu____8808 =
              let uu____8814 =
                let uu____8815 =
                  let uu____8818 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8818)  in
                FStar_SMTEncoding_Util.mkImp uu____8815  in
              ([[typing_pred]], [xx], uu____8814)  in
            mkForall_fuel uu____8808  in
          (uu____8807, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8803  in
      [uu____8802]  in
    uu____8768 :: uu____8800  in
  let mk_ref1 env reft_name uu____8840 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8851 =
        let uu____8855 =
          let uu____8857 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8857]
           in
        (reft_name, uu____8855)  in
      FStar_SMTEncoding_Util.mkApp uu____8851  in
    let refb =
      let uu____8860 =
        let uu____8864 =
          let uu____8866 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8866]
           in
        (reft_name, uu____8864)  in
      FStar_SMTEncoding_Util.mkApp uu____8860  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8870 =
      let uu____8871 =
        let uu____8875 =
          let uu____8876 =
            let uu____8882 =
              let uu____8883 =
                let uu____8886 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8886)  in
              FStar_SMTEncoding_Util.mkImp uu____8883  in
            ([[typing_pred]], [xx; aa], uu____8882)  in
          mkForall_fuel uu____8876  in
        (uu____8875, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Term.Assume uu____8871  in
    let uu____8901 =
      let uu____8903 =
        let uu____8904 =
          let uu____8908 =
            let uu____8909 =
              let uu____8915 =
                let uu____8916 =
                  let uu____8919 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8920 =
                    let uu____8921 =
                      let uu____8924 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8925 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8924, uu____8925)  in
                    FStar_SMTEncoding_Util.mkEq uu____8921  in
                  (uu____8919, uu____8920)  in
                FStar_SMTEncoding_Util.mkImp uu____8916  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8915)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8909  in
          (uu____8908, (Some "ref typing is injective"), "ref_injectivity")
           in
        FStar_SMTEncoding_Term.Assume uu____8904  in
      [uu____8903]  in
    uu____8870 :: uu____8901  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____8967 =
      let uu____8968 =
        let uu____8972 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____8972, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Term.Assume uu____8968  in
    [uu____8967]  in
  let mk_and_interp env conj uu____8983 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____8993 =
        let uu____8997 =
          let uu____8999 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____8999]  in
        ("Valid", uu____8997)  in
      FStar_SMTEncoding_Util.mkApp uu____8993  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9006 =
      let uu____9007 =
        let uu____9011 =
          let uu____9012 =
            let uu____9018 =
              let uu____9019 =
                let uu____9022 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9022, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9019  in
            ([[valid]], [aa; bb], uu____9018)  in
          FStar_SMTEncoding_Util.mkForall uu____9012  in
        (uu____9011, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9007  in
    [uu____9006]  in
  let mk_or_interp env disj uu____9046 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9056 =
        let uu____9060 =
          let uu____9062 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____9062]  in
        ("Valid", uu____9060)  in
      FStar_SMTEncoding_Util.mkApp uu____9056  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9069 =
      let uu____9070 =
        let uu____9074 =
          let uu____9075 =
            let uu____9081 =
              let uu____9082 =
                let uu____9085 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9085, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9082  in
            ([[valid]], [aa; bb], uu____9081)  in
          FStar_SMTEncoding_Util.mkForall uu____9075  in
        (uu____9074, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9070  in
    [uu____9069]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9123 =
        let uu____9127 =
          let uu____9129 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____9129]  in
        ("Valid", uu____9127)  in
      FStar_SMTEncoding_Util.mkApp uu____9123  in
    let uu____9132 =
      let uu____9133 =
        let uu____9137 =
          let uu____9138 =
            let uu____9144 =
              let uu____9145 =
                let uu____9148 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9148, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9145  in
            ([[valid]], [aa; xx1; yy1], uu____9144)  in
          FStar_SMTEncoding_Util.mkForall uu____9138  in
        (uu____9137, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9133  in
    [uu____9132]  in
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
      let uu____9192 =
        let uu____9196 =
          let uu____9198 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____9198]  in
        ("Valid", uu____9196)  in
      FStar_SMTEncoding_Util.mkApp uu____9192  in
    let uu____9201 =
      let uu____9202 =
        let uu____9206 =
          let uu____9207 =
            let uu____9213 =
              let uu____9214 =
                let uu____9217 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9217, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9214  in
            ([[valid]], [aa; bb; xx1; yy1], uu____9213)  in
          FStar_SMTEncoding_Util.mkForall uu____9207  in
        (uu____9206, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9202  in
    [uu____9201]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9255 =
        let uu____9259 =
          let uu____9261 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____9261]  in
        ("Valid", uu____9259)  in
      FStar_SMTEncoding_Util.mkApp uu____9255  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9268 =
      let uu____9269 =
        let uu____9273 =
          let uu____9274 =
            let uu____9280 =
              let uu____9281 =
                let uu____9284 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9284, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9281  in
            ([[valid]], [aa; bb], uu____9280)  in
          FStar_SMTEncoding_Util.mkForall uu____9274  in
        (uu____9273, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9269  in
    [uu____9268]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9318 =
        let uu____9322 =
          let uu____9324 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9324]  in
        ("Valid", uu____9322)  in
      FStar_SMTEncoding_Util.mkApp uu____9318  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9331 =
      let uu____9332 =
        let uu____9336 =
          let uu____9337 =
            let uu____9343 =
              let uu____9344 =
                let uu____9347 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9347, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9344  in
            ([[valid]], [aa; bb], uu____9343)  in
          FStar_SMTEncoding_Util.mkForall uu____9337  in
        (uu____9336, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9332  in
    [uu____9331]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9377 =
        let uu____9381 =
          let uu____9383 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9383]  in
        ("Valid", uu____9381)  in
      FStar_SMTEncoding_Util.mkApp uu____9377  in
    let not_valid_a =
      let uu____9387 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9387  in
    let uu____9389 =
      let uu____9390 =
        let uu____9394 =
          let uu____9395 =
            let uu____9401 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9401)  in
          FStar_SMTEncoding_Util.mkForall uu____9395  in
        (uu____9394, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9390  in
    [uu____9389]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9437 =
        let uu____9441 =
          let uu____9443 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9443]  in
        ("Valid", uu____9441)  in
      FStar_SMTEncoding_Util.mkApp uu____9437  in
    let valid_b_x =
      let uu____9447 =
        let uu____9451 =
          let uu____9453 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9453]  in
        ("Valid", uu____9451)  in
      FStar_SMTEncoding_Util.mkApp uu____9447  in
    let uu____9455 =
      let uu____9456 =
        let uu____9460 =
          let uu____9461 =
            let uu____9467 =
              let uu____9468 =
                let uu____9471 =
                  let uu____9472 =
                    let uu____9478 =
                      let uu____9481 =
                        let uu____9483 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9483]  in
                      [uu____9481]  in
                    let uu____9486 =
                      let uu____9487 =
                        let uu____9490 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9490, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9487  in
                    (uu____9478, [xx1], uu____9486)  in
                  FStar_SMTEncoding_Util.mkForall uu____9472  in
                (uu____9471, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9468  in
            ([[valid]], [aa; bb], uu____9467)  in
          FStar_SMTEncoding_Util.mkForall uu____9461  in
        (uu____9460, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9456  in
    [uu____9455]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9537 =
        let uu____9541 =
          let uu____9543 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9543]  in
        ("Valid", uu____9541)  in
      FStar_SMTEncoding_Util.mkApp uu____9537  in
    let valid_b_x =
      let uu____9547 =
        let uu____9551 =
          let uu____9553 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9553]  in
        ("Valid", uu____9551)  in
      FStar_SMTEncoding_Util.mkApp uu____9547  in
    let uu____9555 =
      let uu____9556 =
        let uu____9560 =
          let uu____9561 =
            let uu____9567 =
              let uu____9568 =
                let uu____9571 =
                  let uu____9572 =
                    let uu____9578 =
                      let uu____9581 =
                        let uu____9583 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9583]  in
                      [uu____9581]  in
                    let uu____9586 =
                      let uu____9587 =
                        let uu____9590 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9590, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9587  in
                    (uu____9578, [xx1], uu____9586)  in
                  FStar_SMTEncoding_Util.mkExists uu____9572  in
                (uu____9571, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9568  in
            ([[valid]], [aa; bb], uu____9567)  in
          FStar_SMTEncoding_Util.mkForall uu____9561  in
        (uu____9560, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9556  in
    [uu____9555]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9626 =
      let uu____9627 =
        let uu____9631 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9632 = varops.mk_unique "typing_range_const"  in
        (uu____9631, (Some "Range_const typing"), uu____9632)  in
      FStar_SMTEncoding_Term.Assume uu____9627  in
    [uu____9626]  in
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
          let uu____9894 =
            FStar_Util.find_opt
              (fun uu____9912  ->
                 match uu____9912 with
                 | (l,uu____9922) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9894 with
          | None  -> []
          | Some (uu____9944,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____9981 = encode_function_type_as_formula None None t env  in
        match uu____9981 with
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
            let uu____10013 =
              (let uu____10014 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10014) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10013
            then
              let uu____10018 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10018 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10030 =
                      let uu____10031 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10031.FStar_Syntax_Syntax.n  in
                    match uu____10030 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10036) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10053  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10056 -> []  in
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
              (let uu____10065 = prims.is lid  in
               if uu____10065
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10070 = prims.mk lid vname  in
                 match uu____10070 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10085 =
                    let uu____10091 = curried_arrow_formals_comp t_norm  in
                    match uu____10091 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10102 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10102
                          then
                            let uu____10103 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10104 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10104.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10104.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10104.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10104.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10104.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10104.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10104.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10104.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10104.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10104.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10104.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10104.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10104.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10104.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10104.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10104.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10104.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10104.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10104.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10104.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10104.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10104.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10104.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10103
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10111 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10111)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10085 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10138 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10138 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10151 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10175  ->
                                     match uu___124_10175 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10178 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10178 with
                                          | (uu____10189,(xxsym,uu____10191))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10201 =
                                                let uu____10202 =
                                                  let uu____10206 =
                                                    let uu____10207 =
                                                      let uu____10213 =
                                                        let uu____10214 =
                                                          let uu____10217 =
                                                            let uu____10218 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10218
                                                             in
                                                          (vapp, uu____10217)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10214
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10213)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10207
                                                     in
                                                  (uu____10206,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10202
                                                 in
                                              [uu____10201])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10229 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10229 with
                                          | (uu____10240,(xxsym,uu____10242))
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
                                              let uu____10256 =
                                                let uu____10257 =
                                                  let uu____10261 =
                                                    let uu____10262 =
                                                      let uu____10268 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10268)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10262
                                                     in
                                                  (uu____10261,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10257
                                                 in
                                              [uu____10256])
                                     | uu____10277 -> []))
                              in
                           let uu____10278 = encode_binders None formals env1
                              in
                           (match uu____10278 with
                            | (vars,guards,env',decls1,uu____10294) ->
                                let uu____10301 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10306 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10306, decls1)
                                  | Some p ->
                                      let uu____10308 = encode_formula p env'
                                         in
                                      (match uu____10308 with
                                       | (g,ds) ->
                                           let uu____10315 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10315,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10301 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10324 =
                                         let uu____10328 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10328)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10324
                                        in
                                     let uu____10333 =
                                       let vname_decl =
                                         let uu____10338 =
                                           let uu____10344 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10349  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10344,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10338
                                          in
                                       let uu____10354 =
                                         let env2 =
                                           let uu___154_10358 = env1  in
                                           {
                                             bindings =
                                               (uu___154_10358.bindings);
                                             depth = (uu___154_10358.depth);
                                             tcenv = (uu___154_10358.tcenv);
                                             warn = (uu___154_10358.warn);
                                             cache = (uu___154_10358.cache);
                                             nolabels =
                                               (uu___154_10358.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10358.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____10359 =
                                           let uu____10360 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10360  in
                                         if uu____10359
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10354 with
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
                                           let uu____10371 =
                                             match formals with
                                             | [] ->
                                                 let uu____10380 =
                                                   let uu____10381 =
                                                     let uu____10383 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10383
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10381
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10380)
                                             | uu____10386 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10391 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10391
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10393 =
                                                     let uu____10397 =
                                                       let uu____10398 =
                                                         let uu____10404 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10404)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10398
                                                        in
                                                     (uu____10397,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10393
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10371 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10333 with
                                      | (decls2,env2) ->
                                          let uu____10428 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10433 =
                                              encode_term res_t1 env'  in
                                            match uu____10433 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10441 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10441,
                                                  decls)
                                             in
                                          (match uu____10428 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10449 =
                                                   let uu____10453 =
                                                     let uu____10454 =
                                                       let uu____10460 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10460)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10454
                                                      in
                                                   (uu____10453,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10449
                                                  in
                                               let freshness =
                                                 let uu____10469 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10469
                                                 then
                                                   let uu____10472 =
                                                     let uu____10473 =
                                                       let uu____10479 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10485 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10479,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10485)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10473
                                                      in
                                                   let uu____10487 =
                                                     let uu____10489 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [uu____10489]  in
                                                   uu____10472 :: uu____10487
                                                 else []  in
                                               let g =
                                                 let uu____10493 =
                                                   let uu____10495 =
                                                     let uu____10497 =
                                                       let uu____10499 =
                                                         let uu____10501 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10501
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10499
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10497
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10495
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10493
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
          let uu____10523 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10523 with
          | None  ->
              let uu____10546 = encode_free_var env x t t_norm []  in
              (match uu____10546 with
               | (decls,env1) ->
                   let uu____10561 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10561 with
                    | (n1,x',uu____10580) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10592) -> ((n1, x1), [], env)
  
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
          let uu____10625 = encode_free_var env lid t tt quals  in
          match uu____10625 with
          | (decls,env1) ->
              let uu____10636 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10636
              then
                let uu____10640 =
                  let uu____10642 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10642  in
                (uu____10640, env1)
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
             (fun uu____10670  ->
                fun lb  ->
                  match uu____10670 with
                  | (decls,env1) ->
                      let uu____10682 =
                        let uu____10686 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10686
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10682 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10700 = FStar_Syntax_Util.head_and_args t  in
    match uu____10700 with
    | (hd1,args) ->
        let uu____10726 =
          let uu____10727 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10727.FStar_Syntax_Syntax.n  in
        (match uu____10726 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10731,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10744 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10759  ->
      fun quals  ->
        match uu____10759 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10808 = FStar_Util.first_N nbinders formals  in
              match uu____10808 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10848  ->
                         fun uu____10849  ->
                           match (uu____10848, uu____10849) with
                           | ((formal,uu____10859),(binder,uu____10861)) ->
                               let uu____10866 =
                                 let uu____10871 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10871)  in
                               FStar_Syntax_Syntax.NT uu____10866) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10876 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10890  ->
                              match uu____10890 with
                              | (x,i) ->
                                  let uu____10897 =
                                    let uu___155_10898 = x  in
                                    let uu____10899 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10898.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10898.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10899
                                    }  in
                                  (uu____10897, i)))
                       in
                    FStar_All.pipe_right uu____10876
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____10911 =
                      let uu____10913 =
                        let uu____10914 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____10914.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10913
                       in
                    let uu____10918 =
                      let uu____10919 = FStar_Syntax_Subst.compress body  in
                      let uu____10920 =
                        let uu____10921 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____10921  in
                      FStar_Syntax_Syntax.extend_app_n uu____10919
                        uu____10920
                       in
                    uu____10918 uu____10911 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10963 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____10963
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_10964 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_10964.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_10964.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_10964.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_10964.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_10964.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_10964.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_10964.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_10964.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_10964.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_10964.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_10964.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_10964.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_10964.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_10964.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_10964.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_10964.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_10964.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_10964.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_10964.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_10964.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_10964.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_10964.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_10964.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____10985 = FStar_Syntax_Util.abs_formals e  in
                match uu____10985 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11034::uu____11035 ->
                         let uu____11043 =
                           let uu____11044 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11044.FStar_Syntax_Syntax.n  in
                         (match uu____11043 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11071 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11071 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11097 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11097
                                   then
                                     let uu____11115 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11115 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11161  ->
                                                   fun uu____11162  ->
                                                     match (uu____11161,
                                                             uu____11162)
                                                     with
                                                     | ((x,uu____11172),
                                                        (b,uu____11174)) ->
                                                         let uu____11179 =
                                                           let uu____11184 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11184)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11179)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11186 =
                                            let uu____11197 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11197)
                                             in
                                          (uu____11186, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11232 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11232 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11284) ->
                              let uu____11289 =
                                let uu____11300 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11300  in
                              (uu____11289, true)
                          | uu____11333 when Prims.op_Negation norm1 ->
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
                          | uu____11335 ->
                              let uu____11336 =
                                let uu____11337 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11338 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11337
                                  uu____11338
                                 in
                              failwith uu____11336)
                     | uu____11351 ->
                         let uu____11352 =
                           let uu____11353 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11353.FStar_Syntax_Syntax.n  in
                         (match uu____11352 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11380 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11380 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11398 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11398 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11446 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11474 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11474
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11481 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11522  ->
                            fun lb  ->
                              match uu____11522 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11573 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11573
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11576 =
                                      let uu____11584 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11584
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11576 with
                                    | (tok,decl,env2) ->
                                        let uu____11609 =
                                          let uu____11616 =
                                            let uu____11622 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11622, tok)  in
                                          uu____11616 :: toks  in
                                        (uu____11609, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11481 with
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
                        | uu____11724 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11729 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11729 vars)
                            else
                              (let uu____11731 =
                                 let uu____11735 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11735)  in
                               FStar_SMTEncoding_Util.mkApp uu____11731)
                         in
                      let uu____11740 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11742  ->
                                 match uu___125_11742 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11743 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11746 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11746)))
                         in
                      if uu____11740
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11766;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11768;
                                FStar_Syntax_Syntax.lbeff = uu____11769;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11810 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____11810 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11825 = env1  in
                                      let uu____11826 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1
                                         in
                                      {
                                        bindings = (uu___159_11825.bindings);
                                        depth = (uu___159_11825.depth);
                                        tcenv = uu____11826;
                                        warn = (uu___159_11825.warn);
                                        cache = (uu___159_11825.cache);
                                        nolabels = (uu___159_11825.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11825.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11825.encode_non_total_function_typ)
                                      }  in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e1 =
                                      let uu____11829 =
                                        FStar_Syntax_Subst.subst univ_subst e
                                         in
                                      FStar_Syntax_Subst.compress uu____11829
                                       in
                                    let uu____11830 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____11830 with
                                     | ((binders,body,uu____11842,uu____11843),curry)
                                         ->
                                         ((let uu____11850 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____11850
                                           then
                                             let uu____11851 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____11852 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11851 uu____11852
                                           else ());
                                          (let uu____11854 =
                                             encode_binders None binders env'
                                              in
                                           match uu____11854 with
                                           | (vars,guards,env'1,binder_decls,uu____11870)
                                               ->
                                               let body1 =
                                                 let uu____11878 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____11878
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____11881 =
                                                 let uu____11886 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____11886
                                                 then
                                                   let uu____11892 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____11893 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____11892, uu____11893)
                                                 else
                                                   (let uu____11899 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____11899))
                                                  in
                                               (match uu____11881 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11913 =
                                                        let uu____11917 =
                                                          let uu____11918 =
                                                            let uu____11924 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____11924)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11918
                                                           in
                                                        let uu____11930 =
                                                          let uu____11932 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____11932
                                                           in
                                                        (uu____11917,
                                                          uu____11930,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11913
                                                       in
                                                    let uu____11934 =
                                                      let uu____11936 =
                                                        let uu____11938 =
                                                          let uu____11940 =
                                                            let uu____11942 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11942
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11940
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11938
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____11936
                                                       in
                                                    (uu____11934, env1))))))
                           | uu____11945 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11964 = varops.fresh "fuel"  in
                             (uu____11964, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____11967 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12006  ->
                                     fun uu____12007  ->
                                       match (uu____12006, uu____12007) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12089 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12089  in
                                           let gtok =
                                             let uu____12091 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12091  in
                                           let env3 =
                                             let uu____12093 =
                                               let uu____12095 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12095
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12093
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____11967 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12179
                                 t_norm uu____12181 =
                                 match (uu____12179, uu____12181) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12206;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12207;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12224 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____12224 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12241 = env2  in
                                            let uu____12242 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1
                                               in
                                            {
                                              bindings =
                                                (uu___160_12241.bindings);
                                              depth = (uu___160_12241.depth);
                                              tcenv = uu____12242;
                                              warn = (uu___160_12241.warn);
                                              cache = (uu___160_12241.cache);
                                              nolabels =
                                                (uu___160_12241.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12241.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12241.encode_non_total_function_typ)
                                            }  in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____12246 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12246
                                            then
                                              let uu____12247 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12248 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12249 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12247 uu____12248
                                                uu____12249
                                            else ());
                                           (let uu____12251 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12251 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12273 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12273
                                                  then
                                                    let uu____12274 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12275 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12276 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12277 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12274 uu____12275
                                                      uu____12276 uu____12277
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12281 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12281 with
                                                  | (vars,guards,env'1,binder_decls,uu____12299)
                                                      ->
                                                      let decl_g =
                                                        let uu____12307 =
                                                          let uu____12313 =
                                                            let uu____12315 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12315
                                                             in
                                                          (g, uu____12313,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12307
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
                                                        let uu____12330 =
                                                          let uu____12334 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12334)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12330
                                                         in
                                                      let gsapp =
                                                        let uu____12340 =
                                                          let uu____12344 =
                                                            let uu____12346 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12346 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12344)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12340
                                                         in
                                                      let gmax =
                                                        let uu____12350 =
                                                          let uu____12354 =
                                                            let uu____12356 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12356 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12354)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12350
                                                         in
                                                      let body1 =
                                                        let uu____12360 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12360
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12362 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12362 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12373
                                                               =
                                                               let uu____12377
                                                                 =
                                                                 let uu____12378
                                                                   =
                                                                   let uu____12386
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
                                                                    uu____12386)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12378
                                                                  in
                                                               let uu____12397
                                                                 =
                                                                 let uu____12399
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____12399
                                                                  in
                                                               (uu____12377,
                                                                 uu____12397,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12373
                                                              in
                                                           let eqn_f =
                                                             let uu____12402
                                                               =
                                                               let uu____12406
                                                                 =
                                                                 let uu____12407
                                                                   =
                                                                   let uu____12413
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12413)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12407
                                                                  in
                                                               (uu____12406,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12402
                                                              in
                                                           let eqn_g' =
                                                             let uu____12421
                                                               =
                                                               let uu____12425
                                                                 =
                                                                 let uu____12426
                                                                   =
                                                                   let uu____12432
                                                                    =
                                                                    let uu____12433
                                                                    =
                                                                    let uu____12436
                                                                    =
                                                                    let uu____12437
                                                                    =
                                                                    let uu____12441
                                                                    =
                                                                    let uu____12443
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12443
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12441)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12437
                                                                     in
                                                                    (gsapp,
                                                                    uu____12436)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12433
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12432)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12426
                                                                  in
                                                               (uu____12425,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12421
                                                              in
                                                           let uu____12455 =
                                                             let uu____12460
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12460
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12477)
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
                                                                    let uu____12492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12492
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12495
                                                                    =
                                                                    let uu____12499
                                                                    =
                                                                    let uu____12500
                                                                    =
                                                                    let uu____12506
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12506)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12500
                                                                     in
                                                                    (uu____12499,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12495
                                                                    in
                                                                 let uu____12517
                                                                   =
                                                                   let uu____12521
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12521
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12529
                                                                    =
                                                                    let uu____12531
                                                                    =
                                                                    let uu____12532
                                                                    =
                                                                    let uu____12536
                                                                    =
                                                                    let uu____12537
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12544
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12547,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12544
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12543)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12537
                                                                     in
                                                                    (uu____12536,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12532
                                                                     in
                                                                    [uu____12531]
                                                                     in
                                                                    (d3,
                                                                    uu____12529)
                                                                    in
                                                                 (match uu____12517
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
                                                           (match uu____12455
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
                               let uu____12582 =
                                 let uu____12589 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12621  ->
                                      fun uu____12622  ->
                                        match (uu____12621, uu____12622) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12698 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12698 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12589
                                  in
                               (match uu____12582 with
                                | (decls2,eqns,env01) ->
                                    let uu____12738 =
                                      let isDeclFun uu___126_12746 =
                                        match uu___126_12746 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12747 -> true
                                        | uu____12753 -> false  in
                                      let uu____12754 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12754
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____12738 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12781 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12781
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
      (let uu____12814 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12814
       then
         let uu____12815 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12815
       else ());
      (let nm =
         let uu____12818 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12818 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12821 = encode_sigelt' env se  in
       match uu____12821 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12830 =
                  let uu____12832 =
                    let uu____12833 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12833  in
                  [uu____12832]  in
                (uu____12830, e)
            | uu____12835 ->
                let uu____12836 =
                  let uu____12838 =
                    let uu____12840 =
                      let uu____12841 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12841  in
                    uu____12840 :: g  in
                  let uu____12842 =
                    let uu____12844 =
                      let uu____12845 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12845  in
                    [uu____12844]  in
                  FStar_List.append uu____12838 uu____12842  in
                (uu____12836, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12853 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12862 =
            let uu____12863 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12863 Prims.op_Negation  in
          if uu____12862
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12883 ->
                   let uu____12884 =
                     let uu____12887 =
                       let uu____12888 =
                         let uu____12903 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12903)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____12888  in
                     FStar_Syntax_Syntax.mk uu____12887  in
                   uu____12884 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____12956 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____12956 with
               | (aname,atok,env2) ->
                   let uu____12966 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____12966 with
                    | (formals,uu____12976) ->
                        let uu____12983 =
                          let uu____12986 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____12986 env2  in
                        (match uu____12983 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12994 =
                                 let uu____12995 =
                                   let uu____13001 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13009  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13001,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____12995
                                  in
                               [uu____12994;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13016 =
                               let aux uu____13045 uu____13046 =
                                 match (uu____13045, uu____13046) with
                                 | ((bv,uu____13073),(env3,acc_sorts,acc)) ->
                                     let uu____13094 = gen_term_var env3 bv
                                        in
                                     (match uu____13094 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13016 with
                              | (uu____13132,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13146 =
                                      let uu____13150 =
                                        let uu____13151 =
                                          let uu____13157 =
                                            let uu____13158 =
                                              let uu____13161 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13161)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13158
                                             in
                                          ([[app]], xs_sorts, uu____13157)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13151
                                         in
                                      (uu____13150, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13146
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13173 =
                                      let uu____13177 =
                                        let uu____13178 =
                                          let uu____13184 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13184)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13178
                                         in
                                      (uu____13177,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13173
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13194 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13194 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13210,uu____13211,uu____13212) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13215 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13215 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13226,t,quals) ->
          let will_encode_definition =
            let uu____13232 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13234  ->
                      match uu___127_13234 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13237 -> false))
               in
            Prims.op_Negation uu____13232  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13243 = encode_top_level_val env fv t quals  in
             match uu____13243 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13255 =
                   let uu____13257 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13257  in
                 (uu____13255, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13262) ->
          let uu____13265 = encode_formula f env  in
          (match uu____13265 with
           | (f1,decls) ->
               let g =
                 let uu____13274 =
                   let uu____13275 =
                     let uu____13279 =
                       let uu____13281 =
                         let uu____13282 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13282  in
                       Some uu____13281  in
                     let uu____13283 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____13279, uu____13283)  in
                   FStar_SMTEncoding_Term.Assume uu____13275  in
                 [uu____13274]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13287,quals,uu____13289) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13297 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13304 =
                       let uu____13309 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13309.FStar_Syntax_Syntax.fv_name  in
                     uu____13304.FStar_Syntax_Syntax.v  in
                   let uu____13313 =
                     let uu____13314 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13314  in
                   if uu____13313
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
                     let uu____13333 = encode_sigelt' env1 val_decl  in
                     match uu____13333 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____13297 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13350,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13352;
                          FStar_Syntax_Syntax.lbtyp = uu____13353;
                          FStar_Syntax_Syntax.lbeff = uu____13354;
                          FStar_Syntax_Syntax.lbdef = uu____13355;_}::[]),uu____13356,uu____13357,uu____13358)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13374 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13374 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13392 =
                   let uu____13396 =
                     let uu____13398 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13398]  in
                   ("Valid", uu____13396)  in
                 FStar_SMTEncoding_Util.mkApp uu____13392  in
               let decls =
                 let uu____13403 =
                   let uu____13405 =
                     let uu____13406 =
                       let uu____13410 =
                         let uu____13411 =
                           let uu____13417 =
                             let uu____13418 =
                               let uu____13421 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13421)  in
                             FStar_SMTEncoding_Util.mkEq uu____13418  in
                           ([[valid_b2t_x]], [xx], uu____13417)  in
                         FStar_SMTEncoding_Util.mkForall uu____13411  in
                       (uu____13410, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Term.Assume uu____13406  in
                   [uu____13405]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13403
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13438,uu____13439,quals,uu____13441) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13449  ->
                  match uu___128_13449 with
                  | FStar_Syntax_Syntax.Discriminator uu____13450 -> true
                  | uu____13451 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13453,lids,quals,uu____13456) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13465 =
                     let uu____13466 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13466.FStar_Ident.idText  in
                   uu____13465 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13468  ->
                     match uu___129_13468 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13469 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13472,quals,uu____13474) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13486  ->
                  match uu___130_13486 with
                  | FStar_Syntax_Syntax.Projector uu____13487 -> true
                  | uu____13490 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13497 = try_lookup_free_var env l  in
          (match uu____13497 with
           | Some uu____13501 -> ([], env)
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
          ((is_rec,bindings),uu____13510,quals,uu____13512) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13526,uu____13527) ->
          let uu____13534 = encode_signature env ses  in
          (match uu____13534 with
           | (g,env1) ->
               let uu____13544 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13554  ->
                         match uu___131_13554 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13555,Some "inversion axiom",uu____13556)
                             -> false
                         | uu____13558 -> true))
                  in
               (match uu____13544 with
                | (g',inversions) ->
                    let uu____13567 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13577  ->
                              match uu___132_13577 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13578 ->
                                  true
                              | uu____13584 -> false))
                       in
                    (match uu____13567 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13595,tps,k,uu____13598,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13609  ->
                    match uu___133_13609 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13610 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13617 = c  in
              match uu____13617 with
              | (name,args,uu____13621,uu____13622,uu____13623) ->
                  let uu____13626 =
                    let uu____13627 =
                      let uu____13633 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13640  ->
                                match uu____13640 with
                                | (uu____13644,sort,uu____13646) -> sort))
                         in
                      (name, uu____13633, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13627  in
                  [uu____13626]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13664 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13667 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13667 FStar_Option.isNone))
               in
            if uu____13664
            then []
            else
              (let uu____13684 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13684 with
               | (xxsym,xx) ->
                   let uu____13690 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13701  ->
                             fun l  ->
                               match uu____13701 with
                               | (out,decls) ->
                                   let uu____13713 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13713 with
                                    | (uu____13719,data_t) ->
                                        let uu____13721 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13721 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13750 =
                                                 let uu____13751 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13751.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13750 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13759,indices) ->
                                                   indices
                                               | uu____13775 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13787  ->
                                                         match uu____13787
                                                         with
                                                         | (x,uu____13791) ->
                                                             let uu____13792
                                                               =
                                                               let uu____13793
                                                                 =
                                                                 let uu____13797
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13797,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13793
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13792)
                                                    env)
                                                in
                                             let uu____13799 =
                                               encode_args indices env1  in
                                             (match uu____13799 with
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
                                                      let uu____13819 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13827
                                                                 =
                                                                 let uu____13830
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13830,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13827)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13819
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13832 =
                                                      let uu____13833 =
                                                        let uu____13836 =
                                                          let uu____13837 =
                                                            let uu____13840 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13840,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13837
                                                           in
                                                        (out, uu____13836)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13833
                                                       in
                                                    (uu____13832,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13690 with
                    | (data_ax,decls) ->
                        let uu____13848 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13848 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13859 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13859 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13862 =
                                 let uu____13866 =
                                   let uu____13867 =
                                     let uu____13873 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13881 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13873,
                                       uu____13881)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13867
                                    in
                                 let uu____13889 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13866, (Some "inversion axiom"),
                                   uu____13889)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13862  in
                             let pattern_guarded_inversion =
                               let uu____13893 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____13893
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____13901 =
                                   let uu____13902 =
                                     let uu____13906 =
                                       let uu____13907 =
                                         let uu____13913 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____13921 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13913, uu____13921)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13907
                                        in
                                     let uu____13929 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____13906, (Some "inversion axiom"),
                                       uu____13929)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____13902
                                    in
                                 [uu____13901]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____13932 =
            let uu____13940 =
              let uu____13941 = FStar_Syntax_Subst.compress k  in
              uu____13941.FStar_Syntax_Syntax.n  in
            match uu____13940 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13970 -> (tps, k)  in
          (match uu____13932 with
           | (formals,res) ->
               let uu____13985 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13985 with
                | (formals1,res1) ->
                    let uu____13992 = encode_binders None formals1 env  in
                    (match uu____13992 with
                     | (vars,guards,env',binder_decls,uu____14007) ->
                         let uu____14014 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14014 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14027 =
                                  let uu____14031 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14031)  in
                                FStar_SMTEncoding_Util.mkApp uu____14027  in
                              let uu____14036 =
                                let tname_decl =
                                  let uu____14042 =
                                    let uu____14043 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14058  ->
                                              match uu____14058 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14066 = varops.next_id ()  in
                                    (tname, uu____14043,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14066, false)
                                     in
                                  constructor_or_logic_type_decl uu____14042
                                   in
                                let uu____14071 =
                                  match vars with
                                  | [] ->
                                      let uu____14078 =
                                        let uu____14079 =
                                          let uu____14081 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14081
                                           in
                                        push_free_var env1 t tname
                                          uu____14079
                                         in
                                      ([], uu____14078)
                                  | uu____14085 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14091 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14091
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14100 =
                                          let uu____14104 =
                                            let uu____14105 =
                                              let uu____14113 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14113)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14105
                                             in
                                          (uu____14104,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14100
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14071 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14036 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14136 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14136 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14150 =
                                               let uu____14151 =
                                                 let uu____14155 =
                                                   let uu____14156 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14156
                                                    in
                                                 (uu____14155,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14151
                                                in
                                             [uu____14150]
                                           else []  in
                                         let uu____14159 =
                                           let uu____14161 =
                                             let uu____14163 =
                                               let uu____14164 =
                                                 let uu____14168 =
                                                   let uu____14169 =
                                                     let uu____14175 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14175)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14169
                                                    in
                                                 (uu____14168, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14164
                                                in
                                             [uu____14163]  in
                                           FStar_List.append karr uu____14161
                                            in
                                         FStar_List.append decls1 uu____14159
                                      in
                                   let aux =
                                     let uu____14184 =
                                       let uu____14186 =
                                         inversion_axioms tapp vars  in
                                       let uu____14188 =
                                         let uu____14190 =
                                           pretype_axiom tapp vars  in
                                         [uu____14190]  in
                                       FStar_List.append uu____14186
                                         uu____14188
                                        in
                                     FStar_List.append kindingAx uu____14184
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14195,uu____14196,uu____14197,uu____14198,uu____14199,uu____14200)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14207,t,uu____14209,n_tps,quals,uu____14212) ->
          let uu____14217 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14217 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14228 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14228 with
                | (formals,t_res) ->
                    let uu____14250 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14250 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14259 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14259 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14297 =
                                            mk_term_projector_name d x  in
                                          (uu____14297,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14299 =
                                  let uu____14309 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14309, true)
                                   in
                                FStar_All.pipe_right uu____14299
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
                              let uu____14331 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14331 with
                               | (tok_typing,decls3) ->
                                   let uu____14338 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14338 with
                                    | (vars',guards',env'',decls_formals,uu____14353)
                                        ->
                                        let uu____14360 =
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
                                        (match uu____14360 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14379 ->
                                                   let uu____14383 =
                                                     let uu____14384 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14384
                                                      in
                                                   [uu____14383]
                                                in
                                             let encode_elim uu____14391 =
                                               let uu____14392 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14392 with
                                               | (head1,args) ->
                                                   let uu____14421 =
                                                     let uu____14422 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14422.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14421 with
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
                                                        let uu____14440 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14440
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
                                                                 | uu____14466
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
                                                                    let uu____14474
                                                                    =
                                                                    let uu____14475
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14475
                                                                     in
                                                                    if
                                                                    uu____14474
                                                                    then
                                                                    let uu____14482
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14482]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14484
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14497
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14497
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14519
                                                                    =
                                                                    let uu____14523
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14523
                                                                     in
                                                                    (match uu____14519
                                                                    with
                                                                    | 
                                                                    (uu____14530,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14536
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14536
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14538
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14538
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
                                                             (match uu____14484
                                                              with
                                                              | (uu____14546,arg_vars,elim_eqns_or_guards,uu____14549)
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
                                                                    let uu____14568
                                                                    =
                                                                    let uu____14572
                                                                    =
                                                                    let uu____14573
                                                                    =
                                                                    let uu____14579
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14585
                                                                    =
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14589)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14586
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14579,
                                                                    uu____14585)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14573
                                                                     in
                                                                    (uu____14572,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14568
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14602
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14602,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14604
                                                                    =
                                                                    let uu____14608
                                                                    =
                                                                    let uu____14609
                                                                    =
                                                                    let uu____14615
                                                                    =
                                                                    let uu____14618
                                                                    =
                                                                    let uu____14620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14620]
                                                                     in
                                                                    [uu____14618]
                                                                     in
                                                                    let uu____14623
                                                                    =
                                                                    let uu____14624
                                                                    =
                                                                    let uu____14627
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14627,
                                                                    uu____14628)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14624
                                                                     in
                                                                    (uu____14615,
                                                                    [x],
                                                                    uu____14623)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14609
                                                                     in
                                                                    let uu____14638
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14608,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14638)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14604
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14643
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
                                                                    (let uu____14658
                                                                    =
                                                                    let uu____14659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14659
                                                                    dapp1  in
                                                                    [uu____14658])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14643
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14663
                                                                    =
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14668
                                                                    =
                                                                    let uu____14674
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14680
                                                                    =
                                                                    let uu____14681
                                                                    =
                                                                    let uu____14684
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14684)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14681
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14674,
                                                                    uu____14680)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14668
                                                                     in
                                                                    (uu____14667,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14663)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14694 ->
                                                        ((let uu____14696 =
                                                            let uu____14697 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14698 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14697
                                                              uu____14698
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14696);
                                                         ([], [])))
                                                in
                                             let uu____14701 = encode_elim ()
                                                in
                                             (match uu____14701 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14713 =
                                                      let uu____14715 =
                                                        let uu____14717 =
                                                          let uu____14719 =
                                                            let uu____14721 =
                                                              let uu____14722
                                                                =
                                                                let uu____14728
                                                                  =
                                                                  let uu____14730
                                                                    =
                                                                    let uu____14731
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14731
                                                                     in
                                                                  Some
                                                                    uu____14730
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14728)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14722
                                                               in
                                                            [uu____14721]  in
                                                          let uu____14734 =
                                                            let uu____14736 =
                                                              let uu____14738
                                                                =
                                                                let uu____14740
                                                                  =
                                                                  let uu____14742
                                                                    =
                                                                    let uu____14744
                                                                    =
                                                                    let uu____14746
                                                                    =
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    let uu____14752
                                                                    =
                                                                    let uu____14758
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14758)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14752
                                                                     in
                                                                    (uu____14751,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14747
                                                                     in
                                                                    let uu____14765
                                                                    =
                                                                    let uu____14767
                                                                    =
                                                                    let uu____14768
                                                                    =
                                                                    let uu____14772
                                                                    =
                                                                    let uu____14773
                                                                    =
                                                                    let uu____14779
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14785
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14779,
                                                                    uu____14785)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14773
                                                                     in
                                                                    (uu____14772,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14768
                                                                     in
                                                                    [uu____14767]
                                                                     in
                                                                    uu____14746
                                                                    ::
                                                                    uu____14765
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14744
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14742
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14740
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14738
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14736
                                                             in
                                                          FStar_List.append
                                                            uu____14719
                                                            uu____14734
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14717
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14715
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14713
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
           (fun uu____14806  ->
              fun se  ->
                match uu____14806 with
                | (g,env1) ->
                    let uu____14818 = encode_sigelt env1 se  in
                    (match uu____14818 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14854 =
        match uu____14854 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14872 ->
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
                 ((let uu____14877 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14877
                   then
                     let uu____14878 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14879 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14880 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14878 uu____14879 uu____14880
                   else ());
                  (let uu____14882 = encode_term t1 env1  in
                   match uu____14882 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14892 =
                         let uu____14896 =
                           let uu____14897 =
                             let uu____14898 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____14898
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____14897  in
                         new_term_constant_from_string env1 x uu____14896  in
                       (match uu____14892 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____14909 = FStar_Options.log_queries ()
                                 in
                              if uu____14909
                              then
                                let uu____14911 =
                                  let uu____14912 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14913 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14914 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14912 uu____14913 uu____14914
                                   in
                                Some uu____14911
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14925,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____14934 = encode_free_var env1 fv t t_norm []  in
                 (match uu____14934 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14953 = encode_sigelt env1 se  in
                 (match uu____14953 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____14963 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____14963 with | (uu____14975,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15020  ->
            match uu____15020 with
            | (l,uu____15027,uu____15028) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15049  ->
            match uu____15049 with
            | (l,uu____15057,uu____15058) ->
                let uu____15063 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____15064 =
                  let uu____15066 =
                    let uu____15067 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15067  in
                  [uu____15066]  in
                uu____15063 :: uu____15064))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15078 =
      let uu____15080 =
        let uu____15081 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15081;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [uu____15080]  in
    FStar_ST.write last_env uu____15078
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____15099 = FStar_ST.read last_env  in
    match uu____15099 with
    | [] -> failwith "No env; call init first!"
    | e::uu____15105 ->
        let uu___161_15107 = e  in
        {
          bindings = (uu___161_15107.bindings);
          depth = (uu___161_15107.depth);
          tcenv;
          warn = (uu___161_15107.warn);
          cache = (uu___161_15107.cache);
          nolabels = (uu___161_15107.nolabels);
          use_zfuel_name = (uu___161_15107.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_15107.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15111 = FStar_ST.read last_env  in
    match uu____15111 with
    | [] -> failwith "Empty env stack"
    | uu____15116::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15124  ->
    let uu____15125 = FStar_ST.read last_env  in
    match uu____15125 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___162_15146 = hd1  in
          {
            bindings = (uu___162_15146.bindings);
            depth = (uu___162_15146.depth);
            tcenv = (uu___162_15146.tcenv);
            warn = (uu___162_15146.warn);
            cache = refs;
            nolabels = (uu___162_15146.nolabels);
            use_zfuel_name = (uu___162_15146.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15146.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15152  ->
    let uu____15153 = FStar_ST.read last_env  in
    match uu____15153 with
    | [] -> failwith "Popping an empty stack"
    | uu____15158::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15166  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15169  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15172  ->
    let uu____15173 = FStar_ST.read last_env  in
    match uu____15173 with
    | hd1::uu____15179::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15185 -> failwith "Impossible"
  
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
        let uu____15230 = FStar_Options.log_queries ()  in
        if uu____15230
        then
          let uu____15232 =
            let uu____15233 =
              let uu____15234 =
                let uu____15235 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15235 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15234  in
            FStar_SMTEncoding_Term.Caption uu____15233  in
          uu____15232 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____15242 = encode_sigelt env se  in
      match uu____15242 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15248 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15248))
  
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
      (let uu____15259 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15259
       then
         let uu____15260 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15260
       else ());
      (let env = get_env tcenv  in
       let uu____15265 =
         encode_signature
           (let uu___163_15269 = env  in
            {
              bindings = (uu___163_15269.bindings);
              depth = (uu___163_15269.depth);
              tcenv = (uu___163_15269.tcenv);
              warn = false;
              cache = (uu___163_15269.cache);
              nolabels = (uu___163_15269.nolabels);
              use_zfuel_name = (uu___163_15269.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15269.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15265 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15281 = FStar_Options.log_queries ()  in
             if uu____15281
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___164_15286 = env1  in
               {
                 bindings = (uu___164_15286.bindings);
                 depth = (uu___164_15286.depth);
                 tcenv = (uu___164_15286.tcenv);
                 warn = true;
                 cache = (uu___164_15286.cache);
                 nolabels = (uu___164_15286.nolabels);
                 use_zfuel_name = (uu___164_15286.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15286.encode_non_total_function_typ)
               });
            (let uu____15288 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15288
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
        (let uu____15323 =
           let uu____15324 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15324.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15323);
        (let env = get_env tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15332 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15353 = aux rest  in
                 (match uu____15353 with
                  | (out,rest1) ->
                      let t =
                        let uu____15371 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____15371 with
                        | Some uu____15375 ->
                            let uu____15376 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____15376
                              x.FStar_Syntax_Syntax.sort
                        | uu____15377 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____15380 =
                        let uu____15382 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15383 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15383.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15383.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____15382 :: out  in
                      (uu____15380, rest1))
             | uu____15386 -> ([], bindings1)  in
           let uu____15390 = aux bindings  in
           match uu____15390 with
           | (closing,bindings1) ->
               let uu____15404 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____15404, bindings1)
            in
         match uu____15332 with
         | (q1,bindings1) ->
             let uu____15417 =
               let uu____15420 =
                 FStar_List.filter
                   (fun uu___134_15422  ->
                      match uu___134_15422 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15423 ->
                          false
                      | uu____15427 -> true) bindings1
                  in
               encode_env_bindings env uu____15420  in
             (match uu____15417 with
              | (env_decls,env1) ->
                  ((let uu____15438 =
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
                    if uu____15438
                    then
                      let uu____15439 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15439
                    else ());
                   (let uu____15441 = encode_formula q1 env1  in
                    match uu____15441 with
                    | (phi,qdecls) ->
                        let uu____15453 =
                          let uu____15456 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15456 phi
                           in
                        (match uu____15453 with
                         | (labels,phi1) ->
                             let uu____15466 = encode_labels labels  in
                             (match uu____15466 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15487 =
                                      let uu____15491 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15492 =
                                        varops.mk_unique "@query"  in
                                      (uu____15491, (Some "query"),
                                        uu____15492)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15487
                                     in
                                  let suffix =
                                    let uu____15496 =
                                      let uu____15498 =
                                        let uu____15500 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15500
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15498
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15496
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15513 = encode_formula q env  in
       match uu____15513 with
       | (f,uu____15517) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15519) -> true
             | uu____15522 -> false)))
  