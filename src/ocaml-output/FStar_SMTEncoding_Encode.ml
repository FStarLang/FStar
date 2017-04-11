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
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }
let print_env : env_t -> Prims.string =
  fun e  ->
    let uu____952 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_956  ->
              match uu___112_956 with
              | Binding_var (x,uu____958) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____960,uu____961,uu____962) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____952 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____995 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      if uu____995
      then
        let uu____997 = FStar_Syntax_Print.term_to_string t  in
        Some uu____997
      else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____1008 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____1008)
  
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
        (let uu___137_1020 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_1020.tcenv);
           warn = (uu___137_1020.warn);
           cache = (uu___137_1020.cache);
           nolabels = (uu___137_1020.nolabels);
           use_zfuel_name = (uu___137_1020.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_1020.encode_non_total_function_typ);
           current_module_name = (uu___137_1020.current_module_name)
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
        (let uu___138_1033 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_1033.depth);
           tcenv = (uu___138_1033.tcenv);
           warn = (uu___138_1033.warn);
           cache = (uu___138_1033.cache);
           nolabels = (uu___138_1033.nolabels);
           use_zfuel_name = (uu___138_1033.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_1033.encode_non_total_function_typ);
           current_module_name = (uu___138_1033.current_module_name)
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
          (let uu___139_1049 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1049.depth);
             tcenv = (uu___139_1049.tcenv);
             warn = (uu___139_1049.warn);
             cache = (uu___139_1049.cache);
             nolabels = (uu___139_1049.nolabels);
             use_zfuel_name = (uu___139_1049.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1049.encode_non_total_function_typ);
             current_module_name = (uu___139_1049.current_module_name)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1059 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1059.depth);
          tcenv = (uu___140_1059.tcenv);
          warn = (uu___140_1059.warn);
          cache = (uu___140_1059.cache);
          nolabels = (uu___140_1059.nolabels);
          use_zfuel_name = (uu___140_1059.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1059.encode_non_total_function_typ);
          current_module_name = (uu___140_1059.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___113_1075  ->
             match uu___113_1075 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1083 -> None)
         in
      let uu____1086 = aux a  in
      match uu____1086 with
      | None  ->
          let a2 = unmangle a  in
          let uu____1093 = aux a2  in
          (match uu____1093 with
           | None  ->
               let uu____1099 =
                 let uu____1100 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____1101 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1100 uu____1101
                  in
               failwith uu____1099
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____1121 =
        let uu___141_1122 = env  in
        let uu____1123 =
          let uu____1125 =
            let uu____1126 =
              let uu____1133 =
                let uu____1135 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1135  in
              (x, fname, uu____1133, None)  in
            Binding_fvar uu____1126  in
          uu____1125 :: (env.bindings)  in
        {
          bindings = uu____1123;
          depth = (uu___141_1122.depth);
          tcenv = (uu___141_1122.tcenv);
          warn = (uu___141_1122.warn);
          cache = (uu___141_1122.cache);
          nolabels = (uu___141_1122.nolabels);
          use_zfuel_name = (uu___141_1122.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1122.encode_non_total_function_typ);
          current_module_name = (uu___141_1122.current_module_name)
        }  in
      (fname, ftok, uu____1121)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___114_1157  ->
           match uu___114_1157 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1179 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1191 =
        lookup_binding env
          (fun uu___115_1193  ->
             match uu___115_1193 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1203 -> None)
         in
      FStar_All.pipe_right uu____1191 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1216 = try_lookup_lid env a  in
      match uu____1216 with
      | None  ->
          let uu____1233 =
            let uu____1234 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____1234  in
          failwith uu____1233
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
          let uu___142_1265 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1265.depth);
            tcenv = (uu___142_1265.tcenv);
            warn = (uu___142_1265.warn);
            cache = (uu___142_1265.cache);
            nolabels = (uu___142_1265.nolabels);
            use_zfuel_name = (uu___142_1265.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1265.encode_non_total_function_typ);
            current_module_name = (uu___142_1265.current_module_name)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1277 = lookup_lid env x  in
        match uu____1277 with
        | (t1,t2,uu____1285) ->
            let t3 =
              let uu____1291 =
                let uu____1295 =
                  let uu____1297 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____1297]  in
                (f, uu____1295)  in
              FStar_SMTEncoding_Util.mkApp uu____1291  in
            let uu___143_1300 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1300.depth);
              tcenv = (uu___143_1300.tcenv);
              warn = (uu___143_1300.warn);
              cache = (uu___143_1300.cache);
              nolabels = (uu___143_1300.nolabels);
              use_zfuel_name = (uu___143_1300.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1300.encode_non_total_function_typ);
              current_module_name = (uu___143_1300.current_module_name)
            }
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1310 = try_lookup_lid env l  in
      match uu____1310 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1337 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1342,fuel::[]) ->
                         let uu____1345 =
                           let uu____1346 =
                             let uu____1347 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____1347 Prims.fst  in
                           FStar_Util.starts_with uu____1346 "fuel"  in
                         if uu____1345
                         then
                           let uu____1349 =
                             let uu____1350 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1350
                               fuel
                              in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1349
                         else Some t
                     | uu____1353 -> Some t)
                | uu____1354 -> None))
  
let lookup_free_var env a =
  let uu____1372 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1372 with
  | Some t -> t
  | None  ->
      let uu____1375 =
        let uu____1376 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format1 "Name not found: %s" uu____1376  in
      failwith uu____1375
  
let lookup_free_var_name env a =
  let uu____1393 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1393 with | (x,uu____1400,uu____1401) -> x 
let lookup_free_var_sym env a =
  let uu____1425 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1425 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1446;
             FStar_SMTEncoding_Term.rng = uu____1447;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1455 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1469 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1478  ->
           match uu___116_1478 with
           | Binding_fvar (uu____1480,nm',tok,uu____1483) when nm = nm' ->
               tok
           | uu____1488 -> None)
  
let mkForall_fuel' n1 uu____1505 =
  match uu____1505 with
  | (pats,vars,body) ->
      let fallback uu____1521 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1524 = FStar_Options.unthrottle_inductives ()  in
      if uu____1524
      then fallback ()
      else
        (let uu____1526 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
         match uu____1526 with
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
                       | uu____1545 -> p))
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
                         let uu____1559 = add_fuel1 guards  in
                         FStar_SMTEncoding_Util.mk_and_l uu____1559
                     | uu____1561 ->
                         let uu____1562 = add_fuel1 [guard]  in
                         FStar_All.pipe_right uu____1562 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1565 -> body  in
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
          let uu____1609 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1609 FStar_Option.isNone
      | uu____1622 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1629 =
        let uu____1630 = FStar_Syntax_Util.un_uinst t  in
        uu____1630.FStar_Syntax_Syntax.n  in
      match uu____1629 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1633,uu____1634,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___117_1663  ->
                  match uu___117_1663 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1664 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1665,uu____1666,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1693 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1693 FStar_Option.isSome
      | uu____1706 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1713 = head_normal env t  in
      if uu____1713
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
    let uu____1724 =
      let uu____1725 = FStar_Syntax_Syntax.null_binder t  in [uu____1725]  in
    let uu____1726 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____1724 uu____1726 None
  
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
                    let uu____1753 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1753
                | s ->
                    let uu____1756 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1756) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___118_1768  ->
    match uu___118_1768 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1769 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1797;
                       FStar_SMTEncoding_Term.rng = uu____1798;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1812) ->
              let uu____1817 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1827 -> false) args vars)
                 in
              if uu____1817 then tok_of_name env f else None
          | (uu____1830,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1  in
              let uu____1833 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1835 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1835))
                 in
              if uu____1833 then Some t1 else None
          | uu____1838 -> None  in
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
      (let uu____1853 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____1853
       then
         let uu____1854 = FStar_Syntax_Print.term_to_string tm  in
         let uu____1855 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1854 uu____1855
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
    | uu____1937 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___119_1940  ->
    match uu___119_1940 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1942 =
          let uu____1946 =
            let uu____1948 =
              let uu____1949 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____1949  in
            [uu____1948]  in
          ("FStar.Char.Char", uu____1946)  in
        FStar_SMTEncoding_Util.mkApp uu____1942
    | FStar_Const.Const_int (i,None ) ->
        let uu____1957 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____1957
    | FStar_Const.Const_int (i,Some uu____1959) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1968) ->
        let uu____1971 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____1971
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1975 =
          let uu____1976 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____1976  in
        failwith uu____1975
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1995 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2003 ->
            let uu____2008 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2008
        | uu____2009 ->
            if norm1
            then let uu____2010 = whnf env t1  in aux false uu____2010
            else
              (let uu____2012 =
                 let uu____2013 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2014 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2013 uu____2014
                  in
               failwith uu____2012)
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
    | uu____2035 ->
        let uu____2036 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2036)
  
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
        (let uu____2179 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____2179
         then
           let uu____2180 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2180
         else ());
        (let uu____2182 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2218  ->
                   fun b  ->
                     match uu____2218 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2261 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2270 = gen_term_var env1 x  in
                           match uu____2270 with
                           | (xxsym,xx,env') ->
                               let uu____2284 =
                                 let uu____2287 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2287 env1 xx
                                  in
                               (match uu____2284 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2261 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2182 with
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
          let uu____2375 = encode_term t env  in
          match uu____2375 with
          | (t1,decls) ->
              let uu____2382 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2382, decls)

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
          let uu____2390 = encode_term t env  in
          match uu____2390 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2399 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2399, decls)
               | Some f ->
                   let uu____2401 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2401, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2408 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2408
       then
         let uu____2409 = FStar_Syntax_Print.tag_of_term t  in
         let uu____2410 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____2411 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2409 uu____2410
           uu____2411
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2416 =
             let uu____2417 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2418 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2419 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2420 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2417
               uu____2418 uu____2419 uu____2420
              in
           failwith uu____2416
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2424 =
             let uu____2425 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2425
              in
           failwith uu____2424
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2430) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2460) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2469 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____2469, [])
       | FStar_Syntax_Syntax.Tm_type uu____2475 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2478) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2484 = encode_const c  in (uu____2484, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____2499 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2499 with
            | (binders1,res) ->
                let uu____2506 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2506
                then
                  let uu____2509 = encode_binders None binders1 env  in
                  (match uu____2509 with
                   | (vars,guards,env',decls,uu____2524) ->
                       let fsym =
                         let uu____2534 = varops.fresh "f"  in
                         (uu____2534, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2537 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2541 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2541.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2541.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2541.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2541.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2541.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2541.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2541.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2541.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2541.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2541.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2541.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2541.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2541.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2541.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2541.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2541.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2541.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2541.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2541.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2541.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2541.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2541.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2541.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____2537 with
                        | (pre_opt,res_t) ->
                            let uu____2548 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2548 with
                             | (res_pred,decls') ->
                                 let uu____2555 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2562 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____2562, [])
                                   | Some pre ->
                                       let uu____2565 =
                                         encode_formula pre env'  in
                                       (match uu____2565 with
                                        | (guard,decls0) ->
                                            let uu____2573 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____2573, decls0))
                                    in
                                 (match uu____2555 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2581 =
                                          let uu____2587 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____2587)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2581
                                         in
                                      let cvars =
                                        let uu____2597 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____2597
                                          (FStar_List.filter
                                             (fun uu____2603  ->
                                                match uu____2603 with
                                                | (x,uu____2607) ->
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
                                      let uu____2618 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2618 with
                                       | Some (t',sorts,uu____2634) ->
                                           let uu____2644 =
                                             let uu____2645 =
                                               let uu____2649 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               (t', uu____2649)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2645
                                              in
                                           (uu____2644, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2665 =
                                               let uu____2666 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2666
                                                in
                                             varops.mk_unique uu____2665  in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2673 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2673
                                             then
                                               let uu____2675 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____2675
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____2681 =
                                               let uu____2685 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____2685)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2681
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
                                             let uu____2693 =
                                               let uu____2697 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____2697, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2693
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
                                             let uu____2710 =
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
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2710
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____2739 =
                                               let uu____2743 =
                                                 let uu____2744 =
                                                   let uu____2750 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2750)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2744
                                                  in
                                               (uu____2743, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2739
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
                     let uu____2781 =
                       let uu____2785 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____2785, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Term.Assume uu____2781  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____2794 =
                       let uu____2798 =
                         let uu____2799 =
                           let uu____2805 =
                             let uu____2806 =
                               let uu____2809 =
                                 let uu____2810 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2810
                                  in
                               (f_has_t, uu____2809)  in
                             FStar_SMTEncoding_Util.mkImp uu____2806  in
                           ([[f_has_t]], [fsym], uu____2805)  in
                         mkForall_fuel uu____2799  in
                       (uu____2798, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Term.Assume uu____2794  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2824 ->
           let uu____2829 =
             let uu____2832 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2832 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2837;
                 FStar_Syntax_Syntax.pos = uu____2838;
                 FStar_Syntax_Syntax.vars = uu____2839;_} ->
                 let uu____2846 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2846 with
                  | (b,f1) ->
                      let uu____2860 =
                        let uu____2861 = FStar_List.hd b  in
                        Prims.fst uu____2861  in
                      (uu____2860, f1))
             | uu____2866 -> failwith "impossible"  in
           (match uu____2829 with
            | (x,f) ->
                let uu____2873 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2873 with
                 | (base_t,decls) ->
                     let uu____2880 = gen_term_var env x  in
                     (match uu____2880 with
                      | (x1,xtm,env') ->
                          let uu____2889 = encode_formula f env'  in
                          (match uu____2889 with
                           | (refinement,decls') ->
                               let uu____2896 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2896 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____2907 =
                                        let uu____2909 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____2913 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____2909
                                          uu____2913
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2907
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2929  ->
                                              match uu____2929 with
                                              | (y,uu____2933) ->
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
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____2952 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2952 with
                                     | Some (t1,uu____2967,uu____2968) ->
                                         let uu____2978 =
                                           let uu____2979 =
                                             let uu____2983 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (t1, uu____2983)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2979
                                            in
                                         (uu____2978, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____3000 =
                                             let uu____3001 =
                                               let uu____3002 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3002
                                                in
                                             Prims.strcat module_name
                                               uu____3001
                                              in
                                           varops.mk_unique uu____3000  in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____3011 =
                                             let uu____3015 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____3015)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3011
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
                                           let uu____3025 =
                                             let uu____3029 =
                                               let uu____3030 =
                                                 let uu____3036 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3036)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3030
                                                in
                                             (uu____3029,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3025
                                            in
                                         let t_kinding =
                                           let uu____3046 =
                                             let uu____3050 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____3050,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3046
                                            in
                                         let t_interp =
                                           let uu____3060 =
                                             let uu____3064 =
                                               let uu____3065 =
                                                 let uu____3071 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3071)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3065
                                                in
                                             let uu____3083 =
                                               let uu____3085 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3085  in
                                             (uu____3064, uu____3083,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____3060
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
             let uu____3113 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3113  in
           let uu____3117 = encode_term_pred None k env ttm  in
           (match uu____3117 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3125 =
                    let uu____3129 =
                      let uu____3130 =
                        let uu____3131 =
                          let uu____3132 = FStar_Unionfind.uvar_id uv  in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3132
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____3131  in
                      varops.mk_unique uu____3130  in
                    (t_has_k, (Some "Uvar typing"), uu____3129)  in
                  FStar_SMTEncoding_Term.Assume uu____3125  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3138 ->
           let uu____3148 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3148 with
            | (head1,args_e) ->
                let uu____3176 =
                  let uu____3184 =
                    let uu____3185 = FStar_Syntax_Subst.compress head1  in
                    uu____3185.FStar_Syntax_Syntax.n  in
                  (uu____3184, args_e)  in
                (match uu____3176 with
                 | (uu____3195,uu____3196) when head_redex env head1 ->
                     let uu____3207 = whnf env t  in
                     encode_term uu____3207 env
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
                     let uu____3281 = encode_term v1 env  in
                     (match uu____3281 with
                      | (v11,decls1) ->
                          let uu____3288 = encode_term v2 env  in
                          (match uu____3288 with
                           | (v21,decls2) ->
                               let uu____3295 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3295,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3297) ->
                     let e0 =
                       let uu____3311 =
                         let uu____3314 =
                           let uu____3315 =
                             let uu____3325 =
                               let uu____3331 = FStar_List.hd args_e  in
                               [uu____3331]  in
                             (head1, uu____3325)  in
                           FStar_Syntax_Syntax.Tm_app uu____3315  in
                         FStar_Syntax_Syntax.mk uu____3314  in
                       uu____3311 None head1.FStar_Syntax_Syntax.pos  in
                     ((let uu____3364 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____3364
                       then
                         let uu____3365 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3365
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
                       (let uu____3369 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        if uu____3369
                        then
                          let uu____3370 =
                            FStar_Syntax_Print.term_to_string e01  in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3370
                        else ());
                       (let e02 =
                          let uu____3373 =
                            let uu____3374 =
                              let uu____3375 =
                                FStar_Syntax_Subst.compress e01  in
                              uu____3375.FStar_Syntax_Syntax.n  in
                            match uu____3374 with
                            | FStar_Syntax_Syntax.Tm_app uu____3378 -> false
                            | uu____3388 -> true  in
                          if uu____3373
                          then e01
                          else
                            (let uu____3390 =
                               FStar_Syntax_Util.head_and_args e01  in
                             match uu____3390 with
                             | (head2,args) ->
                                 let uu____3416 =
                                   let uu____3417 =
                                     let uu____3418 =
                                       FStar_Syntax_Subst.compress head2  in
                                     uu____3418.FStar_Syntax_Syntax.n  in
                                   match uu____3417 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3421 -> false  in
                                 if uu____3416
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3437 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01)
                           in
                        let e =
                          match args_e with
                          | uu____3445::[] -> e02
                          | uu____3458 ->
                              let uu____3464 =
                                let uu____3467 =
                                  let uu____3468 =
                                    let uu____3478 = FStar_List.tl args_e  in
                                    (e02, uu____3478)  in
                                  FStar_Syntax_Syntax.Tm_app uu____3468  in
                                FStar_Syntax_Syntax.mk uu____3467  in
                              uu____3464 None t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3501),(arg,uu____3503)::[]) -> encode_term arg env
                 | uu____3521 ->
                     let uu____3529 = encode_args args_e env  in
                     (match uu____3529 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3562 = encode_term head1 env  in
                            match uu____3562 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3601 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3601 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3643  ->
                                                 fun uu____3644  ->
                                                   match (uu____3643,
                                                           uu____3644)
                                                   with
                                                   | ((bv,uu____3658),
                                                      (a,uu____3660)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3674 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3674
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3679 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3679 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3689 =
                                                   let uu____3693 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3698 =
                                                     let uu____3699 =
                                                       let uu____3700 =
                                                         let uu____3701 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____3701
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3700
                                                        in
                                                     varops.mk_unique
                                                       uu____3699
                                                      in
                                                   (uu____3693,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3698)
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3689
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3718 = lookup_free_var_sym env fv  in
                            match uu____3718 with
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
                                let uu____3756 =
                                  let uu____3757 =
                                    let uu____3760 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____3760 Prims.fst
                                     in
                                  FStar_All.pipe_right uu____3757 Prims.snd
                                   in
                                Some uu____3756
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3779,(FStar_Util.Inl t1,uu____3781),uu____3782)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3820,(FStar_Util.Inr c,uu____3822),uu____3823)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3861 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3881 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3881
                                  in
                               let uu____3882 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____3882 with
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
                                     | uu____3907 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3952 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3952 with
            | (bs1,body1,opening) ->
                let fallback uu____3967 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____3972 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____3972, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3983 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1  in
                      Prims.op_Negation uu____3983
                  | FStar_Util.Inr (eff,uu____3985) ->
                      let uu____3991 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____3991 Prims.op_Negation
                   in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2  in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4036 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___145_4037 = env1.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___145_4037.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___145_4037.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___145_4037.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___145_4037.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___145_4037.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___145_4037.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___145_4037.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___145_4037.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___145_4037.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___145_4037.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___145_4037.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___145_4037.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___145_4037.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___145_4037.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___145_4037.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___145_4037.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___145_4037.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___145_4037.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___145_4037.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___145_4037.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___145_4037.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___145_4037.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___145_4037.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4036 FStar_Syntax_Syntax.U_unknown
                           in
                        let uu____4038 =
                          let uu____4039 = FStar_Syntax_Syntax.mk_Total typ
                             in
                          FStar_Syntax_Util.lcomp_of_comp uu____4039  in
                        FStar_Util.Inl uu____4038
                    | FStar_Util.Inr (eff_name,uu____4046) -> c  in
                  (c1, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4077 =
                        let uu____4078 = lc1.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____4078  in
                      FStar_All.pipe_right uu____4077
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4090 =
                        let uu____4091 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____4091 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4099 =
                          let uu____4100 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____4100  in
                        FStar_All.pipe_right uu____4099
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4104 =
                             let uu____4105 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____4105  in
                           FStar_All.pipe_right uu____4104
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____4116 =
                         let uu____4117 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4117
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4116);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc  in
                     let uu____4132 =
                       (is_impure lc1) &&
                         (let uu____4133 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1
                             in
                          Prims.op_Negation uu____4133)
                        in
                     if uu____4132
                     then fallback ()
                     else
                       (let uu____4137 = encode_binders None bs1 env  in
                        match uu____4137 with
                        | (vars,guards,envbody,decls,uu____4152) ->
                            let uu____4159 =
                              let uu____4167 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1
                                 in
                              if uu____4167
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1)  in
                            (match uu____4159 with
                             | (lc2,body2) ->
                                 let uu____4192 = encode_term body2 envbody
                                    in
                                 (match uu____4192 with
                                  | (body3,decls') ->
                                      let key_body =
                                        let uu____4200 =
                                          let uu____4206 =
                                            let uu____4207 =
                                              let uu____4210 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____4210, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4207
                                             in
                                          ([], vars, uu____4206)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4200
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
                                      let uu____4221 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____4221 with
                                       | Some (t1,uu____4236,uu____4237) ->
                                           let uu____4247 =
                                             let uu____4248 =
                                               let uu____4252 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (t1, uu____4252)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4248
                                              in
                                           (uu____4247, [])
                                       | None  ->
                                           let uu____4263 =
                                             is_eta env vars body3  in
                                           (match uu____4263 with
                                            | Some t1 -> (t1, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____4276 =
                                                      let uu____4277 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4277
                                                       in
                                                    varops.mk_unique
                                                      uu____4276
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  let uu____4282 =
                                                    let uu____4286 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars
                                                       in
                                                    (fsym, uu____4286)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4282
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  let uu____4294 =
                                                    codomain_eff lc2  in
                                                  match uu____4294 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs1 c
                                                         in
                                                      let uu____4301 =
                                                        encode_term_pred None
                                                          tfun env f
                                                         in
                                                      (match uu____4301 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym
                                                              in
                                                           let uu____4308 =
                                                             let uu____4310 =
                                                               let uu____4311
                                                                 =
                                                                 let uu____4315
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                    in
                                                                 (uu____4315,
                                                                   (Some
                                                                    a_name),
                                                                   a_name)
                                                                  in
                                                               FStar_SMTEncoding_Term.Assume
                                                                 uu____4311
                                                                in
                                                             [uu____4310]  in
                                                           FStar_List.append
                                                             decls''
                                                             uu____4308)
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____4323 =
                                                    let uu____4327 =
                                                      let uu____4328 =
                                                        let uu____4334 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          uu____4334)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4328
                                                       in
                                                    (uu____4327,
                                                      (Some a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Term.Assume
                                                    uu____4323
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
           ((uu____4352,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4353;
                          FStar_Syntax_Syntax.lbunivs = uu____4354;
                          FStar_Syntax_Syntax.lbtyp = uu____4355;
                          FStar_Syntax_Syntax.lbeff = uu____4356;
                          FStar_Syntax_Syntax.lbdef = uu____4357;_}::uu____4358),uu____4359)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4377;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4379;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4395 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4408 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4408, [decl_e])))
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
              let uu____4450 = encode_term e1 env  in
              match uu____4450 with
              | (ee1,decls1) ->
                  let uu____4457 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4457 with
                   | (xs,e21) ->
                       let uu____4471 = FStar_List.hd xs  in
                       (match uu____4471 with
                        | (x1,uu____4479) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4481 = encode_body e21 env'  in
                            (match uu____4481 with
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
            let uu____4503 =
              let uu____4507 =
                let uu____4508 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4508  in
              gen_term_var env uu____4507  in
            match uu____4503 with
            | (scrsym,scr',env1) ->
                let uu____4522 = encode_term e env1  in
                (match uu____4522 with
                 | (scr,decls) ->
                     let uu____4529 =
                       let encode_branch b uu____4545 =
                         match uu____4545 with
                         | (else_case,decls1) ->
                             let uu____4556 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4556 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p  in
                                  FStar_List.fold_right
                                    (fun uu____4586  ->
                                       fun uu____4587  ->
                                         match (uu____4586, uu____4587) with
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
                                                       fun uu____4624  ->
                                                         match uu____4624
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1)
                                                in
                                             let uu____4629 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4644 =
                                                     encode_term w1 env2  in
                                                   (match uu____4644 with
                                                    | (w2,decls21) ->
                                                        let uu____4652 =
                                                          let uu____4653 =
                                                            let uu____4656 =
                                                              let uu____4657
                                                                =
                                                                let uu____4660
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4660)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4657
                                                               in
                                                            (guard,
                                                              uu____4656)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4653
                                                           in
                                                        (uu____4652, decls21))
                                                in
                                             (match uu____4629 with
                                              | (guard1,decls21) ->
                                                  let uu____4668 =
                                                    encode_br br env2  in
                                                  (match uu____4668 with
                                                   | (br1,decls3) ->
                                                       let uu____4676 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4676,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4529 with
                      | (match_tm,decls1) ->
                          let uu____4688 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4688, decls1)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4719 ->
          let uu____4720 = encode_one_pat env pat  in [uu____4720]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4732 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4732
       then
         let uu____4733 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4733
       else ());
      (let uu____4735 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4735 with
       | (vars,pat_term) ->
           let uu____4745 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4768  ->
                     fun v1  ->
                       match uu____4768 with
                       | (env1,vars1) ->
                           let uu____4796 = gen_term_var env1 v1  in
                           (match uu____4796 with
                            | (xx,uu____4808,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4745 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4855 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4863 =
                        let uu____4866 = encode_const c  in
                        (scrutinee, uu____4866)  in
                      FStar_SMTEncoding_Util.mkEq uu____4863
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4885 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____4885 with
                        | (uu____4889,uu____4890::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4892 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4913  ->
                                  match uu____4913 with
                                  | (arg,uu____4919) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4929 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4929))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4948 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4963 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4978 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5000  ->
                                  match uu____5000 with
                                  | (arg,uu____5009) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5019 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____5019))
                         in
                      FStar_All.pipe_right uu____4978 FStar_List.flatten
                   in
                let pat_term1 uu____5035 = encode_term pat_term env1  in
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
      let uu____5042 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5057  ->
                fun uu____5058  ->
                  match (uu____5057, uu____5058) with
                  | ((tms,decls),(t,uu____5078)) ->
                      let uu____5089 = encode_term t env  in
                      (match uu____5089 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5042 with | (l1,decls) -> ((FStar_List.rev l1), decls)

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
            let uu____5127 = FStar_Syntax_Util.list_elements e  in
            match uu____5127 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____5145 =
              let uu____5155 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____5155 FStar_Syntax_Util.head_and_args
               in
            match uu____5145 with
            | (head1,args) ->
                let uu____5186 =
                  let uu____5194 =
                    let uu____5195 = FStar_Syntax_Util.un_uinst head1  in
                    uu____5195.FStar_Syntax_Syntax.n  in
                  (uu____5194, args)  in
                (match uu____5186 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5209,uu____5210)::(e,uu____5212)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5243)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5264 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____5297 =
                let uu____5307 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____5307
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____5297 with
              | (head1,args) ->
                  let uu____5336 =
                    let uu____5344 =
                      let uu____5345 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5345.FStar_Syntax_Syntax.n  in
                    (uu____5344, args)  in
                  (match uu____5336 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5358)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5378 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5396 = smt_pat_or t1  in
                (match uu____5396 with
                 | Some e ->
                     let uu____5412 = list_elements1 e  in
                     FStar_All.pipe_right uu____5412
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5429 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5429
                               (FStar_List.map one_pat)))
                 | uu____5443 ->
                     let uu____5447 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5447])
            | uu____5478 ->
                let uu____5480 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5480]
             in
          let uu____5511 =
            let uu____5527 =
              let uu____5528 = FStar_Syntax_Subst.compress t  in
              uu____5528.FStar_Syntax_Syntax.n  in
            match uu____5527 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5558 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5558 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5593;
                            FStar_Syntax_Syntax.effect_name = uu____5594;
                            FStar_Syntax_Syntax.result_typ = uu____5595;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5597)::(post,uu____5599)::(pats,uu____5601)::[];
                            FStar_Syntax_Syntax.flags = uu____5602;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5636 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5636)
                      | uu____5655 -> failwith "impos"))
            | uu____5671 -> failwith "Impos"  in
          match uu____5511 with
          | (binders,pre,post,patterns) ->
              let uu____5715 = encode_binders None binders env  in
              (match uu____5715 with
               | (vars,guards,env1,decls,uu____5730) ->
                   let uu____5737 =
                     let uu____5744 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5775 =
                                 let uu____5780 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5796  ->
                                           match uu____5796 with
                                           | (t1,uu____5803) ->
                                               encode_term t1
                                                 (let uu___146_5806 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___146_5806.bindings);
                                                    depth =
                                                      (uu___146_5806.depth);
                                                    tcenv =
                                                      (uu___146_5806.tcenv);
                                                    warn =
                                                      (uu___146_5806.warn);
                                                    cache =
                                                      (uu___146_5806.cache);
                                                    nolabels =
                                                      (uu___146_5806.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5806.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___146_5806.current_module_name)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5780
                                   FStar_List.unzip
                                  in
                               match uu____5775 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5744 FStar_List.unzip  in
                   (match uu____5737 with
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
                                           let uu____5870 =
                                             let uu____5871 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5871 e
                                              in
                                           uu____5870 :: p))
                               | uu____5872 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5901 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5901 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5909 =
                                           let uu____5910 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5910 tl1
                                            in
                                         aux uu____5909 vars2
                                     | uu____5911 -> pats  in
                                   let uu____5915 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5915 vars)
                           in
                        let env2 =
                          let uu___147_5917 = env1  in
                          {
                            bindings = (uu___147_5917.bindings);
                            depth = (uu___147_5917.depth);
                            tcenv = (uu___147_5917.tcenv);
                            warn = (uu___147_5917.warn);
                            cache = (uu___147_5917.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5917.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5917.encode_non_total_function_typ);
                            current_module_name =
                              (uu___147_5917.current_module_name)
                          }  in
                        let uu____5918 =
                          let uu____5921 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5921 env2  in
                        (match uu____5918 with
                         | (pre1,decls'') ->
                             let uu____5926 =
                               let uu____5929 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5929 env2  in
                             (match uu____5926 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5936 =
                                    let uu____5937 =
                                      let uu____5943 =
                                        let uu____5944 =
                                          let uu____5947 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5947, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5944
                                         in
                                      (pats1, vars, uu____5943)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5937
                                     in
                                  (uu____5936, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5960 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5960
        then
          let uu____5961 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5962 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5961 uu____5962
        else ()  in
      let enc f r l =
        let uu____5989 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6002 = encode_term (Prims.fst x) env  in
                 match uu____6002 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5989 with
        | (decls,args) ->
            let uu____6019 =
              let uu___148_6020 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6020.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6020.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6019, decls)
         in
      let const_op f r uu____6039 = let uu____6042 = f r  in (uu____6042, [])
         in
      let un_op f l =
        let uu____6058 = FStar_List.hd l  in FStar_All.pipe_left f uu____6058
         in
      let bin_op f uu___120_6071 =
        match uu___120_6071 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6079 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6106 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6115  ->
                 match uu____6115 with
                 | (t,uu____6123) ->
                     let uu____6124 = encode_formula t env  in
                     (match uu____6124 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6106 with
        | (decls,phis) ->
            let uu____6141 =
              let uu___149_6142 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6142.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6142.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6141, decls)
         in
      let eq_op r uu___121_6158 =
        match uu___121_6158 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6218 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6218 r [e1; e2]
        | l ->
            let uu____6238 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6238 r l
         in
      let mk_imp1 r uu___122_6257 =
        match uu___122_6257 with
        | (lhs,uu____6261)::(rhs,uu____6263)::[] ->
            let uu____6284 = encode_formula rhs env  in
            (match uu____6284 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6293) ->
                      (l1, decls1)
                  | uu____6296 ->
                      let uu____6297 = encode_formula lhs env  in
                      (match uu____6297 with
                       | (l2,decls2) ->
                           let uu____6304 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6304, (FStar_List.append decls1 decls2)))))
        | uu____6306 -> failwith "impossible"  in
      let mk_ite r uu___123_6321 =
        match uu___123_6321 with
        | (guard,uu____6325)::(_then,uu____6327)::(_else,uu____6329)::[] ->
            let uu____6358 = encode_formula guard env  in
            (match uu____6358 with
             | (g,decls1) ->
                 let uu____6365 = encode_formula _then env  in
                 (match uu____6365 with
                  | (t,decls2) ->
                      let uu____6372 = encode_formula _else env  in
                      (match uu____6372 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6381 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6400 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6400  in
      let connectives =
        let uu____6412 =
          let uu____6421 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6421)  in
        let uu____6434 =
          let uu____6444 =
            let uu____6453 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6453)  in
          let uu____6466 =
            let uu____6476 =
              let uu____6486 =
                let uu____6495 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6495)  in
              let uu____6508 =
                let uu____6518 =
                  let uu____6528 =
                    let uu____6537 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6537)  in
                  [uu____6528;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6518  in
              uu____6486 :: uu____6508  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6476  in
          uu____6444 :: uu____6466  in
        uu____6412 :: uu____6434  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6699 = encode_formula phi' env  in
            (match uu____6699 with
             | (phi2,decls) ->
                 let uu____6706 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6706, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6707 ->
            let uu____6712 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6712 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6741 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6741 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6749;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6751;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6767 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6767 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6799::(x,uu____6801)::(t,uu____6803)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6837 = encode_term x env  in
                 (match uu____6837 with
                  | (x1,decls) ->
                      let uu____6844 = encode_term t env  in
                      (match uu____6844 with
                       | (t1,decls') ->
                           let uu____6851 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6851, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6855)::(msg,uu____6857)::(phi2,uu____6859)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6893 =
                   let uu____6896 =
                     let uu____6897 = FStar_Syntax_Subst.compress r  in
                     uu____6897.FStar_Syntax_Syntax.n  in
                   let uu____6900 =
                     let uu____6901 = FStar_Syntax_Subst.compress msg  in
                     uu____6901.FStar_Syntax_Syntax.n  in
                   (uu____6896, uu____6900)  in
                 (match uu____6893 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6908))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6924 -> fallback phi2)
             | uu____6927 when head_redex env head2 ->
                 let uu____6935 = whnf env phi1  in
                 encode_formula uu____6935 env
             | uu____6936 ->
                 let uu____6944 = encode_term phi1 env  in
                 (match uu____6944 with
                  | (tt,decls) ->
                      let uu____6951 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6952 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6952.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6952.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6951, decls)))
        | uu____6955 ->
            let uu____6956 = encode_term phi1 env  in
            (match uu____6956 with
             | (tt,decls) ->
                 let uu____6963 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6964 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6964.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6964.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6963, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____6991 = encode_binders None bs env1  in
        match uu____6991 with
        | (vars,guards,env2,decls,uu____7013) ->
            let uu____7020 =
              let uu____7027 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7050 =
                          let uu____7055 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7069  ->
                                    match uu____7069 with
                                    | (t,uu____7075) ->
                                        encode_term t
                                          (let uu___152_7076 = env2  in
                                           {
                                             bindings =
                                               (uu___152_7076.bindings);
                                             depth = (uu___152_7076.depth);
                                             tcenv = (uu___152_7076.tcenv);
                                             warn = (uu___152_7076.warn);
                                             cache = (uu___152_7076.cache);
                                             nolabels =
                                               (uu___152_7076.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7076.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___152_7076.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____7055 FStar_List.unzip
                           in
                        match uu____7050 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7027 FStar_List.unzip  in
            (match uu____7020 with
             | (pats,decls') ->
                 let uu____7128 = encode_formula body env2  in
                 (match uu____7128 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7147;
                             FStar_SMTEncoding_Term.rng = uu____7148;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7156 -> guards  in
                      let uu____7159 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7159, body1,
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
                (fun uu____7193  ->
                   match uu____7193 with
                   | (x,uu____7197) ->
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
               let uu____7203 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7209 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7209) uu____7203 tl1
                in
             let uu____7211 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7223  ->
                       match uu____7223 with
                       | (b,uu____7227) ->
                           let uu____7228 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7228))
                in
             (match uu____7211 with
              | None  -> ()
              | Some (x,uu____7232) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7242 =
                    let uu____7243 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7243
                     in
                  FStar_Errors.warn pos uu____7242)
          in
       let uu____7244 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7244 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7250 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7286  ->
                     match uu____7286 with
                     | (l,uu____7296) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7250 with
            | None  -> fallback phi1
            | Some (uu____7319,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7348 = encode_q_body env vars pats body  in
             match uu____7348 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7374 =
                     let uu____7380 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7380)  in
                   FStar_SMTEncoding_Term.mkForall uu____7374
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7392 = encode_q_body env vars pats body  in
             match uu____7392 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7417 =
                   let uu____7418 =
                     let uu____7424 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7424)  in
                   FStar_SMTEncoding_Term.mkExists uu____7418
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7417, decls))))

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
  let uu____7473 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7473 with
  | (asym,a) ->
      let uu____7478 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7478 with
       | (xsym,x) ->
           let uu____7483 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7483 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7513 =
                      let uu____7519 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7519, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7513  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7534 =
                      let uu____7538 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7538)  in
                    FStar_SMTEncoding_Util.mkApp uu____7534  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7546 =
                    let uu____7548 =
                      let uu____7550 =
                        let uu____7552 =
                          let uu____7553 =
                            let uu____7557 =
                              let uu____7558 =
                                let uu____7564 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7564)  in
                              FStar_SMTEncoding_Util.mkForall uu____7558  in
                            (uu____7557, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7553  in
                        let uu____7573 =
                          let uu____7575 =
                            let uu____7576 =
                              let uu____7580 =
                                let uu____7581 =
                                  let uu____7587 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7587)  in
                                FStar_SMTEncoding_Util.mkForall uu____7581
                                 in
                              (uu____7580,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7576  in
                          [uu____7575]  in
                        uu____7552 :: uu____7573  in
                      xtok_decl :: uu____7550  in
                    xname_decl :: uu____7548  in
                  (xtok1, uu____7546)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7636 =
                    let uu____7644 =
                      let uu____7650 =
                        let uu____7651 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7651
                         in
                      quant axy uu____7650  in
                    (FStar_Syntax_Const.op_Eq, uu____7644)  in
                  let uu____7657 =
                    let uu____7666 =
                      let uu____7674 =
                        let uu____7680 =
                          let uu____7681 =
                            let uu____7682 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7682  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7681
                           in
                        quant axy uu____7680  in
                      (FStar_Syntax_Const.op_notEq, uu____7674)  in
                    let uu____7688 =
                      let uu____7697 =
                        let uu____7705 =
                          let uu____7711 =
                            let uu____7712 =
                              let uu____7713 =
                                let uu____7716 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7717 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7716, uu____7717)  in
                              FStar_SMTEncoding_Util.mkLT uu____7713  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7712
                             in
                          quant xy uu____7711  in
                        (FStar_Syntax_Const.op_LT, uu____7705)  in
                      let uu____7723 =
                        let uu____7732 =
                          let uu____7740 =
                            let uu____7746 =
                              let uu____7747 =
                                let uu____7748 =
                                  let uu____7751 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7752 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7751, uu____7752)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7748  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7747
                               in
                            quant xy uu____7746  in
                          (FStar_Syntax_Const.op_LTE, uu____7740)  in
                        let uu____7758 =
                          let uu____7767 =
                            let uu____7775 =
                              let uu____7781 =
                                let uu____7782 =
                                  let uu____7783 =
                                    let uu____7786 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7787 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7786, uu____7787)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7783  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7782
                                 in
                              quant xy uu____7781  in
                            (FStar_Syntax_Const.op_GT, uu____7775)  in
                          let uu____7793 =
                            let uu____7802 =
                              let uu____7810 =
                                let uu____7816 =
                                  let uu____7817 =
                                    let uu____7818 =
                                      let uu____7821 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7822 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7821, uu____7822)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7818
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7817
                                   in
                                quant xy uu____7816  in
                              (FStar_Syntax_Const.op_GTE, uu____7810)  in
                            let uu____7828 =
                              let uu____7837 =
                                let uu____7845 =
                                  let uu____7851 =
                                    let uu____7852 =
                                      let uu____7853 =
                                        let uu____7856 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7857 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7856, uu____7857)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7853
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7852
                                     in
                                  quant xy uu____7851  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7845)
                                 in
                              let uu____7863 =
                                let uu____7872 =
                                  let uu____7880 =
                                    let uu____7886 =
                                      let uu____7887 =
                                        let uu____7888 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7888
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7887
                                       in
                                    quant qx uu____7886  in
                                  (FStar_Syntax_Const.op_Minus, uu____7880)
                                   in
                                let uu____7894 =
                                  let uu____7903 =
                                    let uu____7911 =
                                      let uu____7917 =
                                        let uu____7918 =
                                          let uu____7919 =
                                            let uu____7922 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7923 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7922, uu____7923)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7919
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7918
                                         in
                                      quant xy uu____7917  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7911)
                                     in
                                  let uu____7929 =
                                    let uu____7938 =
                                      let uu____7946 =
                                        let uu____7952 =
                                          let uu____7953 =
                                            let uu____7954 =
                                              let uu____7957 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7958 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7957, uu____7958)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7954
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7953
                                           in
                                        quant xy uu____7952  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7946)
                                       in
                                    let uu____7964 =
                                      let uu____7973 =
                                        let uu____7981 =
                                          let uu____7987 =
                                            let uu____7988 =
                                              let uu____7989 =
                                                let uu____7992 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____7993 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____7992, uu____7993)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7989
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7988
                                             in
                                          quant xy uu____7987  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7981)
                                         in
                                      let uu____7999 =
                                        let uu____8008 =
                                          let uu____8016 =
                                            let uu____8022 =
                                              let uu____8023 =
                                                let uu____8024 =
                                                  let uu____8027 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8028 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8027, uu____8028)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8024
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8023
                                               in
                                            quant xy uu____8022  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8016)
                                           in
                                        let uu____8034 =
                                          let uu____8043 =
                                            let uu____8051 =
                                              let uu____8057 =
                                                let uu____8058 =
                                                  let uu____8059 =
                                                    let uu____8062 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8063 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8062, uu____8063)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8059
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8058
                                                 in
                                              quant xy uu____8057  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8051)
                                             in
                                          let uu____8069 =
                                            let uu____8078 =
                                              let uu____8086 =
                                                let uu____8092 =
                                                  let uu____8093 =
                                                    let uu____8094 =
                                                      let uu____8097 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8098 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8097,
                                                        uu____8098)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8094
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8093
                                                   in
                                                quant xy uu____8092  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8086)
                                               in
                                            let uu____8104 =
                                              let uu____8113 =
                                                let uu____8121 =
                                                  let uu____8127 =
                                                    let uu____8128 =
                                                      let uu____8129 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8129
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8128
                                                     in
                                                  quant qx uu____8127  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8121)
                                                 in
                                              [uu____8113]  in
                                            uu____8078 :: uu____8104  in
                                          uu____8043 :: uu____8069  in
                                        uu____8008 :: uu____8034  in
                                      uu____7973 :: uu____7999  in
                                    uu____7938 :: uu____7964  in
                                  uu____7903 :: uu____7929  in
                                uu____7872 :: uu____7894  in
                              uu____7837 :: uu____7863  in
                            uu____7802 :: uu____7828  in
                          uu____7767 :: uu____7793  in
                        uu____7732 :: uu____7758  in
                      uu____7697 :: uu____7723  in
                    uu____7666 :: uu____7688  in
                  uu____7636 :: uu____7657  in
                let mk1 l v1 =
                  let uu____8257 =
                    let uu____8262 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8294  ->
                              match uu____8294 with
                              | (l',uu____8303) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8262
                      (FStar_Option.map
                         (fun uu____8336  ->
                            match uu____8336 with | (uu____8347,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8257 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8388  ->
                          match uu____8388 with
                          | (l',uu____8397) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8423 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____8423 with
        | (xxsym,xx) ->
            let uu____8428 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____8428 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____8436 =
                   let uu____8440 =
                     let uu____8441 =
                       let uu____8447 =
                         let uu____8448 =
                           let uu____8451 =
                             let uu____8452 =
                               let uu____8455 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____8455)  in
                             FStar_SMTEncoding_Util.mkEq uu____8452  in
                           (xx_has_type, uu____8451)  in
                         FStar_SMTEncoding_Util.mkImp uu____8448  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8447)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____8441  in
                   let uu____8468 =
                     let uu____8469 =
                       let uu____8470 =
                         let uu____8471 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____8471  in
                       Prims.strcat module_name uu____8470  in
                     varops.mk_unique uu____8469  in
                   (uu____8440, (Some "pretyping"), uu____8468)  in
                 FStar_SMTEncoding_Term.Assume uu____8436)
  
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
    let uu____8501 =
      let uu____8502 =
        let uu____8506 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8506, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8502  in
    let uu____8508 =
      let uu____8510 =
        let uu____8511 =
          let uu____8515 =
            let uu____8516 =
              let uu____8522 =
                let uu____8523 =
                  let uu____8526 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8526)  in
                FStar_SMTEncoding_Util.mkImp uu____8523  in
              ([[typing_pred]], [xx], uu____8522)  in
            mkForall_fuel uu____8516  in
          (uu____8515, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8511  in
      [uu____8510]  in
    uu____8501 :: uu____8508  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8554 =
      let uu____8555 =
        let uu____8559 =
          let uu____8560 =
            let uu____8566 =
              let uu____8569 =
                let uu____8571 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8571]  in
              [uu____8569]  in
            let uu____8574 =
              let uu____8575 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8575 tt  in
            (uu____8566, [bb], uu____8574)  in
          FStar_SMTEncoding_Util.mkForall uu____8560  in
        (uu____8559, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8555  in
    let uu____8586 =
      let uu____8588 =
        let uu____8589 =
          let uu____8593 =
            let uu____8594 =
              let uu____8600 =
                let uu____8601 =
                  let uu____8604 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8604)  in
                FStar_SMTEncoding_Util.mkImp uu____8601  in
              ([[typing_pred]], [xx], uu____8600)  in
            mkForall_fuel uu____8594  in
          (uu____8593, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8589  in
      [uu____8588]  in
    uu____8554 :: uu____8586  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8638 =
        let uu____8639 =
          let uu____8643 =
            let uu____8645 =
              let uu____8647 =
                let uu____8649 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8650 =
                  let uu____8652 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8652]  in
                uu____8649 :: uu____8650  in
              tt :: uu____8647  in
            tt :: uu____8645  in
          ("Prims.Precedes", uu____8643)  in
        FStar_SMTEncoding_Util.mkApp uu____8639  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8638  in
    let precedes_y_x =
      let uu____8655 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8655  in
    let uu____8657 =
      let uu____8658 =
        let uu____8662 =
          let uu____8663 =
            let uu____8669 =
              let uu____8672 =
                let uu____8674 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8674]  in
              [uu____8672]  in
            let uu____8677 =
              let uu____8678 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8678 tt  in
            (uu____8669, [bb], uu____8677)  in
          FStar_SMTEncoding_Util.mkForall uu____8663  in
        (uu____8662, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8658  in
    let uu____8689 =
      let uu____8691 =
        let uu____8692 =
          let uu____8696 =
            let uu____8697 =
              let uu____8703 =
                let uu____8704 =
                  let uu____8707 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8707)  in
                FStar_SMTEncoding_Util.mkImp uu____8704  in
              ([[typing_pred]], [xx], uu____8703)  in
            mkForall_fuel uu____8697  in
          (uu____8696, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8692  in
      let uu____8720 =
        let uu____8722 =
          let uu____8723 =
            let uu____8727 =
              let uu____8728 =
                let uu____8734 =
                  let uu____8735 =
                    let uu____8738 =
                      let uu____8739 =
                        let uu____8741 =
                          let uu____8743 =
                            let uu____8745 =
                              let uu____8746 =
                                let uu____8749 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8750 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8749, uu____8750)  in
                              FStar_SMTEncoding_Util.mkGT uu____8746  in
                            let uu____8751 =
                              let uu____8753 =
                                let uu____8754 =
                                  let uu____8757 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8758 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8757, uu____8758)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8754  in
                              let uu____8759 =
                                let uu____8761 =
                                  let uu____8762 =
                                    let uu____8765 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8766 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8765, uu____8766)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8762  in
                                [uu____8761]  in
                              uu____8753 :: uu____8759  in
                            uu____8745 :: uu____8751  in
                          typing_pred_y :: uu____8743  in
                        typing_pred :: uu____8741  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8739  in
                    (uu____8738, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8735  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8734)
                 in
              mkForall_fuel uu____8728  in
            (uu____8727, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Term.Assume uu____8723  in
        [uu____8722]  in
      uu____8691 :: uu____8720  in
    uu____8657 :: uu____8689  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8796 =
      let uu____8797 =
        let uu____8801 =
          let uu____8802 =
            let uu____8808 =
              let uu____8811 =
                let uu____8813 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8813]  in
              [uu____8811]  in
            let uu____8816 =
              let uu____8817 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8817 tt  in
            (uu____8808, [bb], uu____8816)  in
          FStar_SMTEncoding_Util.mkForall uu____8802  in
        (uu____8801, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8797  in
    let uu____8828 =
      let uu____8830 =
        let uu____8831 =
          let uu____8835 =
            let uu____8836 =
              let uu____8842 =
                let uu____8843 =
                  let uu____8846 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8846)  in
                FStar_SMTEncoding_Util.mkImp uu____8843  in
              ([[typing_pred]], [xx], uu____8842)  in
            mkForall_fuel uu____8836  in
          (uu____8835, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8831  in
      [uu____8830]  in
    uu____8796 :: uu____8828  in
  let mk_ref1 env reft_name uu____8868 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8879 =
        let uu____8883 =
          let uu____8885 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8885]
           in
        (reft_name, uu____8883)  in
      FStar_SMTEncoding_Util.mkApp uu____8879  in
    let refb =
      let uu____8888 =
        let uu____8892 =
          let uu____8894 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8894]
           in
        (reft_name, uu____8892)  in
      FStar_SMTEncoding_Util.mkApp uu____8888  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8898 =
      let uu____8899 =
        let uu____8903 =
          let uu____8904 =
            let uu____8910 =
              let uu____8911 =
                let uu____8914 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8914)  in
              FStar_SMTEncoding_Util.mkImp uu____8911  in
            ([[typing_pred]], [xx; aa], uu____8910)  in
          mkForall_fuel uu____8904  in
        (uu____8903, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Term.Assume uu____8899  in
    let uu____8929 =
      let uu____8931 =
        let uu____8932 =
          let uu____8936 =
            let uu____8937 =
              let uu____8943 =
                let uu____8944 =
                  let uu____8947 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8948 =
                    let uu____8949 =
                      let uu____8952 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8953 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8952, uu____8953)  in
                    FStar_SMTEncoding_Util.mkEq uu____8949  in
                  (uu____8947, uu____8948)  in
                FStar_SMTEncoding_Util.mkImp uu____8944  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8943)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8937  in
          (uu____8936, (Some "ref typing is injective"), "ref_injectivity")
           in
        FStar_SMTEncoding_Term.Assume uu____8932  in
      [uu____8931]  in
    uu____8898 :: uu____8929  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____8995 =
      let uu____8996 =
        let uu____9000 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9000, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Term.Assume uu____8996  in
    [uu____8995]  in
  let mk_and_interp env conj uu____9011 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9021 =
        let uu____9025 =
          let uu____9027 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____9027]  in
        ("Valid", uu____9025)  in
      FStar_SMTEncoding_Util.mkApp uu____9021  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9034 =
      let uu____9035 =
        let uu____9039 =
          let uu____9040 =
            let uu____9046 =
              let uu____9047 =
                let uu____9050 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9050, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9047  in
            ([[valid]], [aa; bb], uu____9046)  in
          FStar_SMTEncoding_Util.mkForall uu____9040  in
        (uu____9039, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9035  in
    [uu____9034]  in
  let mk_or_interp env disj uu____9074 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9084 =
        let uu____9088 =
          let uu____9090 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____9090]  in
        ("Valid", uu____9088)  in
      FStar_SMTEncoding_Util.mkApp uu____9084  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9097 =
      let uu____9098 =
        let uu____9102 =
          let uu____9103 =
            let uu____9109 =
              let uu____9110 =
                let uu____9113 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9113, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9110  in
            ([[valid]], [aa; bb], uu____9109)  in
          FStar_SMTEncoding_Util.mkForall uu____9103  in
        (uu____9102, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9098  in
    [uu____9097]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9151 =
        let uu____9155 =
          let uu____9157 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____9157]  in
        ("Valid", uu____9155)  in
      FStar_SMTEncoding_Util.mkApp uu____9151  in
    let uu____9160 =
      let uu____9161 =
        let uu____9165 =
          let uu____9166 =
            let uu____9172 =
              let uu____9173 =
                let uu____9176 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9176, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9173  in
            ([[valid]], [aa; xx1; yy1], uu____9172)  in
          FStar_SMTEncoding_Util.mkForall uu____9166  in
        (uu____9165, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9161  in
    [uu____9160]  in
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
      let uu____9220 =
        let uu____9224 =
          let uu____9226 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____9226]  in
        ("Valid", uu____9224)  in
      FStar_SMTEncoding_Util.mkApp uu____9220  in
    let uu____9229 =
      let uu____9230 =
        let uu____9234 =
          let uu____9235 =
            let uu____9241 =
              let uu____9242 =
                let uu____9245 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9245, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9242  in
            ([[valid]], [aa; bb; xx1; yy1], uu____9241)  in
          FStar_SMTEncoding_Util.mkForall uu____9235  in
        (uu____9234, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9230  in
    [uu____9229]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9283 =
        let uu____9287 =
          let uu____9289 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____9289]  in
        ("Valid", uu____9287)  in
      FStar_SMTEncoding_Util.mkApp uu____9283  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9296 =
      let uu____9297 =
        let uu____9301 =
          let uu____9302 =
            let uu____9308 =
              let uu____9309 =
                let uu____9312 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9312, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9309  in
            ([[valid]], [aa; bb], uu____9308)  in
          FStar_SMTEncoding_Util.mkForall uu____9302  in
        (uu____9301, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9297  in
    [uu____9296]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9346 =
        let uu____9350 =
          let uu____9352 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9352]  in
        ("Valid", uu____9350)  in
      FStar_SMTEncoding_Util.mkApp uu____9346  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9359 =
      let uu____9360 =
        let uu____9364 =
          let uu____9365 =
            let uu____9371 =
              let uu____9372 =
                let uu____9375 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9375, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9372  in
            ([[valid]], [aa; bb], uu____9371)  in
          FStar_SMTEncoding_Util.mkForall uu____9365  in
        (uu____9364, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9360  in
    [uu____9359]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9405 =
        let uu____9409 =
          let uu____9411 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9411]  in
        ("Valid", uu____9409)  in
      FStar_SMTEncoding_Util.mkApp uu____9405  in
    let not_valid_a =
      let uu____9415 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9415  in
    let uu____9417 =
      let uu____9418 =
        let uu____9422 =
          let uu____9423 =
            let uu____9429 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9429)  in
          FStar_SMTEncoding_Util.mkForall uu____9423  in
        (uu____9422, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9418  in
    [uu____9417]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9465 =
        let uu____9469 =
          let uu____9471 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9471]  in
        ("Valid", uu____9469)  in
      FStar_SMTEncoding_Util.mkApp uu____9465  in
    let valid_b_x =
      let uu____9475 =
        let uu____9479 =
          let uu____9481 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9481]  in
        ("Valid", uu____9479)  in
      FStar_SMTEncoding_Util.mkApp uu____9475  in
    let uu____9483 =
      let uu____9484 =
        let uu____9488 =
          let uu____9489 =
            let uu____9495 =
              let uu____9496 =
                let uu____9499 =
                  let uu____9500 =
                    let uu____9506 =
                      let uu____9509 =
                        let uu____9511 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9511]  in
                      [uu____9509]  in
                    let uu____9514 =
                      let uu____9515 =
                        let uu____9518 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9518, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9515  in
                    (uu____9506, [xx1], uu____9514)  in
                  FStar_SMTEncoding_Util.mkForall uu____9500  in
                (uu____9499, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9496  in
            ([[valid]], [aa; bb], uu____9495)  in
          FStar_SMTEncoding_Util.mkForall uu____9489  in
        (uu____9488, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9484  in
    [uu____9483]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9565 =
        let uu____9569 =
          let uu____9571 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9571]  in
        ("Valid", uu____9569)  in
      FStar_SMTEncoding_Util.mkApp uu____9565  in
    let valid_b_x =
      let uu____9575 =
        let uu____9579 =
          let uu____9581 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9581]  in
        ("Valid", uu____9579)  in
      FStar_SMTEncoding_Util.mkApp uu____9575  in
    let uu____9583 =
      let uu____9584 =
        let uu____9588 =
          let uu____9589 =
            let uu____9595 =
              let uu____9596 =
                let uu____9599 =
                  let uu____9600 =
                    let uu____9606 =
                      let uu____9609 =
                        let uu____9611 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9611]  in
                      [uu____9609]  in
                    let uu____9614 =
                      let uu____9615 =
                        let uu____9618 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9618, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9615  in
                    (uu____9606, [xx1], uu____9614)  in
                  FStar_SMTEncoding_Util.mkExists uu____9600  in
                (uu____9599, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9596  in
            ([[valid]], [aa; bb], uu____9595)  in
          FStar_SMTEncoding_Util.mkForall uu____9589  in
        (uu____9588, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9584  in
    [uu____9583]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9654 =
      let uu____9655 =
        let uu____9659 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9660 = varops.mk_unique "typing_range_const"  in
        (uu____9659, (Some "Range_const typing"), uu____9660)  in
      FStar_SMTEncoding_Term.Assume uu____9655  in
    [uu____9654]  in
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
          let uu____9922 =
            FStar_Util.find_opt
              (fun uu____9940  ->
                 match uu____9940 with
                 | (l,uu____9950) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9922 with
          | None  -> []
          | Some (uu____9972,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____10009 = encode_function_type_as_formula None None t env  in
        match uu____10009 with
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
            let uu____10041 =
              (let uu____10042 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10042) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10041
            then
              let uu____10046 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10046 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10058 =
                      let uu____10059 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10059.FStar_Syntax_Syntax.n  in
                    match uu____10058 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10064) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10081  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10084 -> []  in
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
              (let uu____10093 = prims.is lid  in
               if uu____10093
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10098 = prims.mk lid vname  in
                 match uu____10098 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10113 =
                    let uu____10119 = curried_arrow_formals_comp t_norm  in
                    match uu____10119 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10130 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10130
                          then
                            let uu____10131 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10132 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10132.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10132.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10132.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10132.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10132.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10132.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10132.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10132.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10132.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10132.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10132.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10132.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10132.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10132.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10132.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10132.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10132.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10132.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10132.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10132.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10132.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10132.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10132.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10131
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10139 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10139)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10113 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10166 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10166 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10179 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10203  ->
                                     match uu___124_10203 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10206 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10206 with
                                          | (uu____10217,(xxsym,uu____10219))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10229 =
                                                let uu____10230 =
                                                  let uu____10234 =
                                                    let uu____10235 =
                                                      let uu____10241 =
                                                        let uu____10242 =
                                                          let uu____10245 =
                                                            let uu____10246 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10246
                                                             in
                                                          (vapp, uu____10245)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10242
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10241)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10235
                                                     in
                                                  (uu____10234,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10230
                                                 in
                                              [uu____10229])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10257 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10257 with
                                          | (uu____10268,(xxsym,uu____10270))
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
                                              let uu____10284 =
                                                let uu____10285 =
                                                  let uu____10289 =
                                                    let uu____10290 =
                                                      let uu____10296 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10296)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10290
                                                     in
                                                  (uu____10289,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10285
                                                 in
                                              [uu____10284])
                                     | uu____10305 -> []))
                              in
                           let uu____10306 = encode_binders None formals env1
                              in
                           (match uu____10306 with
                            | (vars,guards,env',decls1,uu____10322) ->
                                let uu____10329 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10334 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10334, decls1)
                                  | Some p ->
                                      let uu____10336 = encode_formula p env'
                                         in
                                      (match uu____10336 with
                                       | (g,ds) ->
                                           let uu____10343 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10343,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10329 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10352 =
                                         let uu____10356 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10356)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10352
                                        in
                                     let uu____10361 =
                                       let vname_decl =
                                         let uu____10366 =
                                           let uu____10372 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10377  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10372,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10366
                                          in
                                       let uu____10382 =
                                         let env2 =
                                           let uu___154_10386 = env1  in
                                           {
                                             bindings =
                                               (uu___154_10386.bindings);
                                             depth = (uu___154_10386.depth);
                                             tcenv = (uu___154_10386.tcenv);
                                             warn = (uu___154_10386.warn);
                                             cache = (uu___154_10386.cache);
                                             nolabels =
                                               (uu___154_10386.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10386.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___154_10386.current_module_name)
                                           }  in
                                         let uu____10387 =
                                           let uu____10388 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10388  in
                                         if uu____10387
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10382 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10398::uu____10399 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort)
                                                    in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff
                                                    in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff]  in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)]
                                                    in
                                                 let guarded_tok_typing =
                                                   let uu____10422 =
                                                     let uu____10428 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing
                                                        in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10428)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10422
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10442 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                              in
                                           let uu____10444 =
                                             match formals with
                                             | [] ->
                                                 let uu____10453 =
                                                   let uu____10454 =
                                                     let uu____10456 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10456
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10454
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10453)
                                             | uu____10459 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10464 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10464
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10466 =
                                                     let uu____10470 =
                                                       let uu____10471 =
                                                         let uu____10477 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10477)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10471
                                                        in
                                                     (uu____10470,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10466
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10444 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10361 with
                                      | (decls2,env2) ->
                                          let uu____10501 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10506 =
                                              encode_term res_t1 env'  in
                                            match uu____10506 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10514 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10514,
                                                  decls)
                                             in
                                          (match uu____10501 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10522 =
                                                   let uu____10526 =
                                                     let uu____10527 =
                                                       let uu____10533 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10533)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10527
                                                      in
                                                   (uu____10526,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10522
                                                  in
                                               let freshness =
                                                 let uu____10542 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10542
                                                 then
                                                   let uu____10545 =
                                                     let uu____10546 =
                                                       let uu____10552 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10558 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10552,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10558)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10546
                                                      in
                                                   let uu____10560 =
                                                     let uu____10562 =
                                                       pretype_axiom env2
                                                         vapp vars
                                                        in
                                                     [uu____10562]  in
                                                   uu____10545 :: uu____10560
                                                 else []  in
                                               let g =
                                                 let uu____10566 =
                                                   let uu____10568 =
                                                     let uu____10570 =
                                                       let uu____10572 =
                                                         let uu____10574 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10574
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10572
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10570
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10568
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10566
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
          let uu____10596 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10596 with
          | None  ->
              let uu____10619 = encode_free_var env x t t_norm []  in
              (match uu____10619 with
               | (decls,env1) ->
                   let uu____10634 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10634 with
                    | (n1,x',uu____10653) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10665) -> ((n1, x1), [], env)
  
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
          let uu____10698 = encode_free_var env lid t tt quals  in
          match uu____10698 with
          | (decls,env1) ->
              let uu____10709 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10709
              then
                let uu____10713 =
                  let uu____10715 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10715  in
                (uu____10713, env1)
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
             (fun uu____10743  ->
                fun lb  ->
                  match uu____10743 with
                  | (decls,env1) ->
                      let uu____10755 =
                        let uu____10759 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10759
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10755 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10773 = FStar_Syntax_Util.head_and_args t  in
    match uu____10773 with
    | (hd1,args) ->
        let uu____10799 =
          let uu____10800 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10800.FStar_Syntax_Syntax.n  in
        (match uu____10799 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10804,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10817 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10832  ->
      fun quals  ->
        match uu____10832 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10881 = FStar_Util.first_N nbinders formals  in
              match uu____10881 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10921  ->
                         fun uu____10922  ->
                           match (uu____10921, uu____10922) with
                           | ((formal,uu____10932),(binder,uu____10934)) ->
                               let uu____10939 =
                                 let uu____10944 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10944)  in
                               FStar_Syntax_Syntax.NT uu____10939) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10949 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10963  ->
                              match uu____10963 with
                              | (x,i) ->
                                  let uu____10970 =
                                    let uu___155_10971 = x  in
                                    let uu____10972 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10971.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_10971.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10972
                                    }  in
                                  (uu____10970, i)))
                       in
                    FStar_All.pipe_right uu____10949
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____10984 =
                      let uu____10986 =
                        let uu____10987 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____10987.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10986
                       in
                    let uu____10991 =
                      let uu____10992 = FStar_Syntax_Subst.compress body  in
                      let uu____10993 =
                        let uu____10994 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____10994  in
                      FStar_Syntax_Syntax.extend_app_n uu____10992
                        uu____10993
                       in
                    uu____10991 uu____10984 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11036 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____11036
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11037 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11037.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11037.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11037.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11037.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11037.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11037.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11037.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11037.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11037.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11037.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11037.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11037.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11037.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11037.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11037.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11037.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11037.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11037.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11037.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11037.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11037.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11037.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11037.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____11058 = FStar_Syntax_Util.abs_formals e  in
                match uu____11058 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11107::uu____11108 ->
                         let uu____11116 =
                           let uu____11117 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11117.FStar_Syntax_Syntax.n  in
                         (match uu____11116 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11144 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11144 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11170 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11170
                                   then
                                     let uu____11188 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11188 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11234  ->
                                                   fun uu____11235  ->
                                                     match (uu____11234,
                                                             uu____11235)
                                                     with
                                                     | ((x,uu____11245),
                                                        (b,uu____11247)) ->
                                                         let uu____11252 =
                                                           let uu____11257 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11257)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11252)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11259 =
                                            let uu____11270 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11270)
                                             in
                                          (uu____11259, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11305 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11305 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11357) ->
                              let uu____11362 =
                                let uu____11373 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11373  in
                              (uu____11362, true)
                          | uu____11406 when Prims.op_Negation norm1 ->
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
                          | uu____11408 ->
                              let uu____11409 =
                                let uu____11410 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11411 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11410
                                  uu____11411
                                 in
                              failwith uu____11409)
                     | uu____11424 ->
                         let uu____11425 =
                           let uu____11426 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11426.FStar_Syntax_Syntax.n  in
                         (match uu____11425 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11453 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11453 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11471 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11471 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11519 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11547 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11547
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11554 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11595  ->
                            fun lb  ->
                              match uu____11595 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11646 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11646
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11649 =
                                      let uu____11657 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11657
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11649 with
                                    | (tok,decl,env2) ->
                                        let uu____11682 =
                                          let uu____11689 =
                                            let uu____11695 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11695, tok)  in
                                          uu____11689 :: toks  in
                                        (uu____11682, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11554 with
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
                        | uu____11797 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11802 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11802 vars)
                            else
                              (let uu____11804 =
                                 let uu____11808 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11808)  in
                               FStar_SMTEncoding_Util.mkApp uu____11804)
                         in
                      let uu____11813 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11815  ->
                                 match uu___125_11815 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11816 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11819 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11819)))
                         in
                      if uu____11813
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11839;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11841;
                                FStar_Syntax_Syntax.lbeff = uu____11842;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11883 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____11883 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11898 = env1  in
                                      let uu____11899 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1
                                         in
                                      {
                                        bindings = (uu___159_11898.bindings);
                                        depth = (uu___159_11898.depth);
                                        tcenv = uu____11899;
                                        warn = (uu___159_11898.warn);
                                        cache = (uu___159_11898.cache);
                                        nolabels = (uu___159_11898.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11898.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11898.encode_non_total_function_typ);
                                        current_module_name =
                                          (uu___159_11898.current_module_name)
                                      }  in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e1 =
                                      let uu____11902 =
                                        FStar_Syntax_Subst.subst univ_subst e
                                         in
                                      FStar_Syntax_Subst.compress uu____11902
                                       in
                                    let uu____11903 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____11903 with
                                     | ((binders,body,uu____11915,uu____11916),curry)
                                         ->
                                         ((let uu____11923 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____11923
                                           then
                                             let uu____11924 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____11925 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11924 uu____11925
                                           else ());
                                          (let uu____11927 =
                                             encode_binders None binders env'
                                              in
                                           match uu____11927 with
                                           | (vars,guards,env'1,binder_decls,uu____11943)
                                               ->
                                               let body1 =
                                                 let uu____11951 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____11951
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____11954 =
                                                 let uu____11959 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____11959
                                                 then
                                                   let uu____11965 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____11966 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____11965, uu____11966)
                                                 else
                                                   (let uu____11972 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____11972))
                                                  in
                                               (match uu____11954 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11986 =
                                                        let uu____11990 =
                                                          let uu____11991 =
                                                            let uu____11997 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____11997)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11991
                                                           in
                                                        let uu____12003 =
                                                          let uu____12005 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____12005
                                                           in
                                                        (uu____11990,
                                                          uu____12003,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____11986
                                                       in
                                                    let uu____12007 =
                                                      let uu____12009 =
                                                        let uu____12011 =
                                                          let uu____12013 =
                                                            let uu____12015 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12015
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12013
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12011
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____12009
                                                       in
                                                    (uu____12007, env1))))))
                           | uu____12018 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12037 = varops.fresh "fuel"  in
                             (uu____12037, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____12040 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12079  ->
                                     fun uu____12080  ->
                                       match (uu____12079, uu____12080) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12162 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12162  in
                                           let gtok =
                                             let uu____12164 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12164  in
                                           let env3 =
                                             let uu____12166 =
                                               let uu____12168 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12168
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12166
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____12040 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12252
                                 t_norm uu____12254 =
                                 match (uu____12252, uu____12254) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12279;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12280;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12297 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____12297 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12314 = env2  in
                                            let uu____12315 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1
                                               in
                                            {
                                              bindings =
                                                (uu___160_12314.bindings);
                                              depth = (uu___160_12314.depth);
                                              tcenv = uu____12315;
                                              warn = (uu___160_12314.warn);
                                              cache = (uu___160_12314.cache);
                                              nolabels =
                                                (uu___160_12314.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12314.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12314.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___160_12314.current_module_name)
                                            }  in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____12319 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12319
                                            then
                                              let uu____12320 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12321 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12322 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12320 uu____12321
                                                uu____12322
                                            else ());
                                           (let uu____12324 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12324 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12346 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12346
                                                  then
                                                    let uu____12347 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12348 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12349 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12350 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12347 uu____12348
                                                      uu____12349 uu____12350
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12354 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12354 with
                                                  | (vars,guards,env'1,binder_decls,uu____12372)
                                                      ->
                                                      let decl_g =
                                                        let uu____12380 =
                                                          let uu____12386 =
                                                            let uu____12388 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12388
                                                             in
                                                          (g, uu____12386,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12380
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
                                                        let uu____12403 =
                                                          let uu____12407 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12407)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12403
                                                         in
                                                      let gsapp =
                                                        let uu____12413 =
                                                          let uu____12417 =
                                                            let uu____12419 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12419 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12417)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12413
                                                         in
                                                      let gmax =
                                                        let uu____12423 =
                                                          let uu____12427 =
                                                            let uu____12429 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12429 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12427)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12423
                                                         in
                                                      let body1 =
                                                        let uu____12433 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12433
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12435 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12435 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12446
                                                               =
                                                               let uu____12450
                                                                 =
                                                                 let uu____12451
                                                                   =
                                                                   let uu____12459
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
                                                                    uu____12459)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12451
                                                                  in
                                                               let uu____12470
                                                                 =
                                                                 let uu____12472
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____12472
                                                                  in
                                                               (uu____12450,
                                                                 uu____12470,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12446
                                                              in
                                                           let eqn_f =
                                                             let uu____12475
                                                               =
                                                               let uu____12479
                                                                 =
                                                                 let uu____12480
                                                                   =
                                                                   let uu____12486
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12486)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12480
                                                                  in
                                                               (uu____12479,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12475
                                                              in
                                                           let eqn_g' =
                                                             let uu____12494
                                                               =
                                                               let uu____12498
                                                                 =
                                                                 let uu____12499
                                                                   =
                                                                   let uu____12505
                                                                    =
                                                                    let uu____12506
                                                                    =
                                                                    let uu____12509
                                                                    =
                                                                    let uu____12510
                                                                    =
                                                                    let uu____12514
                                                                    =
                                                                    let uu____12516
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12516
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12514)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12510
                                                                     in
                                                                    (gsapp,
                                                                    uu____12509)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12506
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12505)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12499
                                                                  in
                                                               (uu____12498,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12494
                                                              in
                                                           let uu____12528 =
                                                             let uu____12533
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12533
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12550)
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
                                                                    let uu____12565
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12565
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12568
                                                                    =
                                                                    let uu____12572
                                                                    =
                                                                    let uu____12573
                                                                    =
                                                                    let uu____12579
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12579)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12573
                                                                     in
                                                                    (uu____12572,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12568
                                                                    in
                                                                 let uu____12590
                                                                   =
                                                                   let uu____12594
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12594
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12602
                                                                    =
                                                                    let uu____12604
                                                                    =
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12609
                                                                    =
                                                                    let uu____12610
                                                                    =
                                                                    let uu____12616
                                                                    =
                                                                    let uu____12617
                                                                    =
                                                                    let uu____12620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12620,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12617
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12616)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12610
                                                                     in
                                                                    (uu____12609,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12605
                                                                     in
                                                                    [uu____12604]
                                                                     in
                                                                    (d3,
                                                                    uu____12602)
                                                                    in
                                                                 (match uu____12590
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
                                                           (match uu____12528
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
                               let uu____12655 =
                                 let uu____12662 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12694  ->
                                      fun uu____12695  ->
                                        match (uu____12694, uu____12695) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12771 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12771 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12662
                                  in
                               (match uu____12655 with
                                | (decls2,eqns,env01) ->
                                    let uu____12811 =
                                      let isDeclFun uu___126_12819 =
                                        match uu___126_12819 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12820 -> true
                                        | uu____12826 -> false  in
                                      let uu____12827 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12827
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____12811 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12854 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12854
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
      (let uu____12887 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12887
       then
         let uu____12888 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12888
       else ());
      (let nm =
         let uu____12891 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12891 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12894 = encode_sigelt' env se  in
       match uu____12894 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12903 =
                  let uu____12905 =
                    let uu____12906 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12906  in
                  [uu____12905]  in
                (uu____12903, e)
            | uu____12908 ->
                let uu____12909 =
                  let uu____12911 =
                    let uu____12913 =
                      let uu____12914 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12914  in
                    uu____12913 :: g  in
                  let uu____12915 =
                    let uu____12917 =
                      let uu____12918 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12918  in
                    [uu____12917]  in
                  FStar_List.append uu____12911 uu____12915  in
                (uu____12909, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12926 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12935 =
            let uu____12936 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12936 Prims.op_Negation  in
          if uu____12935
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12956 ->
                   let uu____12957 =
                     let uu____12960 =
                       let uu____12961 =
                         let uu____12976 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12976)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____12961  in
                     FStar_Syntax_Syntax.mk uu____12960  in
                   uu____12957 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____13029 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____13029 with
               | (aname,atok,env2) ->
                   let uu____13039 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____13039 with
                    | (formals,uu____13049) ->
                        let uu____13056 =
                          let uu____13059 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____13059 env2  in
                        (match uu____13056 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13067 =
                                 let uu____13068 =
                                   let uu____13074 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13082  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13074,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____13068
                                  in
                               [uu____13067;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13089 =
                               let aux uu____13118 uu____13119 =
                                 match (uu____13118, uu____13119) with
                                 | ((bv,uu____13146),(env3,acc_sorts,acc)) ->
                                     let uu____13167 = gen_term_var env3 bv
                                        in
                                     (match uu____13167 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13089 with
                              | (uu____13205,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13219 =
                                      let uu____13223 =
                                        let uu____13224 =
                                          let uu____13230 =
                                            let uu____13231 =
                                              let uu____13234 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13234)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13231
                                             in
                                          ([[app]], xs_sorts, uu____13230)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13224
                                         in
                                      (uu____13223, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13219
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13246 =
                                      let uu____13250 =
                                        let uu____13251 =
                                          let uu____13257 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13257)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13251
                                         in
                                      (uu____13250,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13246
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13267 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13267 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13283,uu____13284,uu____13285) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13288 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13288 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13299,t,quals) ->
          let will_encode_definition =
            let uu____13305 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13307  ->
                      match uu___127_13307 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13310 -> false))
               in
            Prims.op_Negation uu____13305  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13316 = encode_top_level_val env fv t quals  in
             match uu____13316 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13328 =
                   let uu____13330 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13330  in
                 (uu____13328, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13335) ->
          let uu____13338 = encode_formula f env  in
          (match uu____13338 with
           | (f1,decls) ->
               let g =
                 let uu____13347 =
                   let uu____13348 =
                     let uu____13352 =
                       let uu____13354 =
                         let uu____13355 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13355  in
                       Some uu____13354  in
                     let uu____13356 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____13352, uu____13356)  in
                   FStar_SMTEncoding_Term.Assume uu____13348  in
                 [uu____13347]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13360,quals,uu____13362) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13370 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13377 =
                       let uu____13382 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13382.FStar_Syntax_Syntax.fv_name  in
                     uu____13377.FStar_Syntax_Syntax.v  in
                   let uu____13386 =
                     let uu____13387 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13387  in
                   if uu____13386
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
                     let uu____13406 = encode_sigelt' env1 val_decl  in
                     match uu____13406 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____13370 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13423,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13425;
                          FStar_Syntax_Syntax.lbtyp = uu____13426;
                          FStar_Syntax_Syntax.lbeff = uu____13427;
                          FStar_Syntax_Syntax.lbdef = uu____13428;_}::[]),uu____13429,uu____13430,uu____13431)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13447 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13447 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13465 =
                   let uu____13469 =
                     let uu____13471 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13471]  in
                   ("Valid", uu____13469)  in
                 FStar_SMTEncoding_Util.mkApp uu____13465  in
               let decls =
                 let uu____13476 =
                   let uu____13478 =
                     let uu____13479 =
                       let uu____13483 =
                         let uu____13484 =
                           let uu____13490 =
                             let uu____13491 =
                               let uu____13494 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13494)  in
                             FStar_SMTEncoding_Util.mkEq uu____13491  in
                           ([[valid_b2t_x]], [xx], uu____13490)  in
                         FStar_SMTEncoding_Util.mkForall uu____13484  in
                       (uu____13483, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Term.Assume uu____13479  in
                   [uu____13478]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13476
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13511,uu____13512,quals,uu____13514) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13522  ->
                  match uu___128_13522 with
                  | FStar_Syntax_Syntax.Discriminator uu____13523 -> true
                  | uu____13524 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13526,lids,quals,uu____13529) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13538 =
                     let uu____13539 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13539.FStar_Ident.idText  in
                   uu____13538 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13541  ->
                     match uu___129_13541 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13542 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13545,quals,uu____13547) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13559  ->
                  match uu___130_13559 with
                  | FStar_Syntax_Syntax.Projector uu____13560 -> true
                  | uu____13563 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13570 = try_lookup_free_var env l  in
          (match uu____13570 with
           | Some uu____13574 -> ([], env)
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
          ((is_rec,bindings),uu____13583,quals,uu____13585) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13599,uu____13600) ->
          let uu____13607 = encode_signature env ses  in
          (match uu____13607 with
           | (g,env1) ->
               let uu____13617 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13627  ->
                         match uu___131_13627 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13628,Some "inversion axiom",uu____13629)
                             -> false
                         | uu____13631 -> true))
                  in
               (match uu____13617 with
                | (g',inversions) ->
                    let uu____13640 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13650  ->
                              match uu___132_13650 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13651 ->
                                  true
                              | uu____13657 -> false))
                       in
                    (match uu____13640 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13668,tps,k,uu____13671,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13682  ->
                    match uu___133_13682 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13683 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13690 = c  in
              match uu____13690 with
              | (name,args,uu____13694,uu____13695,uu____13696) ->
                  let uu____13699 =
                    let uu____13700 =
                      let uu____13706 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13713  ->
                                match uu____13713 with
                                | (uu____13717,sort,uu____13719) -> sort))
                         in
                      (name, uu____13706, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13700  in
                  [uu____13699]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13737 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13740 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13740 FStar_Option.isNone))
               in
            if uu____13737
            then []
            else
              (let uu____13757 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13757 with
               | (xxsym,xx) ->
                   let uu____13763 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13774  ->
                             fun l  ->
                               match uu____13774 with
                               | (out,decls) ->
                                   let uu____13786 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13786 with
                                    | (uu____13792,data_t) ->
                                        let uu____13794 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13794 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13823 =
                                                 let uu____13824 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13824.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13823 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13832,indices) ->
                                                   indices
                                               | uu____13848 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13860  ->
                                                         match uu____13860
                                                         with
                                                         | (x,uu____13864) ->
                                                             let uu____13865
                                                               =
                                                               let uu____13866
                                                                 =
                                                                 let uu____13870
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13870,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13866
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13865)
                                                    env)
                                                in
                                             let uu____13872 =
                                               encode_args indices env1  in
                                             (match uu____13872 with
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
                                                      let uu____13892 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13900
                                                                 =
                                                                 let uu____13903
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13903,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13900)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13892
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13905 =
                                                      let uu____13906 =
                                                        let uu____13909 =
                                                          let uu____13910 =
                                                            let uu____13913 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13913,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13910
                                                           in
                                                        (out, uu____13909)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13906
                                                       in
                                                    (uu____13905,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13763 with
                    | (data_ax,decls) ->
                        let uu____13921 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13921 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13932 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13932 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13935 =
                                 let uu____13939 =
                                   let uu____13940 =
                                     let uu____13946 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13954 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13946,
                                       uu____13954)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13940
                                    in
                                 let uu____13962 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13939, (Some "inversion axiom"),
                                   uu____13962)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13935  in
                             let pattern_guarded_inversion =
                               let uu____13966 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____13966
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____13974 =
                                   let uu____13975 =
                                     let uu____13979 =
                                       let uu____13980 =
                                         let uu____13986 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____13994 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13986, uu____13994)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13980
                                        in
                                     let uu____14002 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____13979, (Some "inversion axiom"),
                                       uu____14002)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____13975
                                    in
                                 [uu____13974]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____14005 =
            let uu____14013 =
              let uu____14014 = FStar_Syntax_Subst.compress k  in
              uu____14014.FStar_Syntax_Syntax.n  in
            match uu____14013 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14043 -> (tps, k)  in
          (match uu____14005 with
           | (formals,res) ->
               let uu____14058 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____14058 with
                | (formals1,res1) ->
                    let uu____14065 = encode_binders None formals1 env  in
                    (match uu____14065 with
                     | (vars,guards,env',binder_decls,uu____14080) ->
                         let uu____14087 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14087 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14100 =
                                  let uu____14104 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14104)  in
                                FStar_SMTEncoding_Util.mkApp uu____14100  in
                              let uu____14109 =
                                let tname_decl =
                                  let uu____14115 =
                                    let uu____14116 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14131  ->
                                              match uu____14131 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14139 = varops.next_id ()  in
                                    (tname, uu____14116,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14139, false)
                                     in
                                  constructor_or_logic_type_decl uu____14115
                                   in
                                let uu____14144 =
                                  match vars with
                                  | [] ->
                                      let uu____14151 =
                                        let uu____14152 =
                                          let uu____14154 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14154
                                           in
                                        push_free_var env1 t tname
                                          uu____14152
                                         in
                                      ([], uu____14151)
                                  | uu____14158 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14164 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14164
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14173 =
                                          let uu____14177 =
                                            let uu____14178 =
                                              let uu____14186 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14186)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14178
                                             in
                                          (uu____14177,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14173
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14144 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14109 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14209 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14209 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14223 =
                                               let uu____14224 =
                                                 let uu____14228 =
                                                   let uu____14229 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14229
                                                    in
                                                 (uu____14228,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14224
                                                in
                                             [uu____14223]
                                           else []  in
                                         let uu____14232 =
                                           let uu____14234 =
                                             let uu____14236 =
                                               let uu____14237 =
                                                 let uu____14241 =
                                                   let uu____14242 =
                                                     let uu____14248 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14248)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14242
                                                    in
                                                 (uu____14241, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14237
                                                in
                                             [uu____14236]  in
                                           FStar_List.append karr uu____14234
                                            in
                                         FStar_List.append decls1 uu____14232
                                      in
                                   let aux =
                                     let uu____14257 =
                                       let uu____14259 =
                                         inversion_axioms tapp vars  in
                                       let uu____14261 =
                                         let uu____14263 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____14263]  in
                                       FStar_List.append uu____14259
                                         uu____14261
                                        in
                                     FStar_List.append kindingAx uu____14257
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14268,uu____14269,uu____14270,uu____14271,uu____14272,uu____14273)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14280,t,uu____14282,n_tps,quals,uu____14285) ->
          let uu____14290 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14290 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14301 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14301 with
                | (formals,t_res) ->
                    let uu____14323 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14323 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14332 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14332 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14370 =
                                            mk_term_projector_name d x  in
                                          (uu____14370,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14372 =
                                  let uu____14382 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14382, true)
                                   in
                                FStar_All.pipe_right uu____14372
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
                              let uu____14404 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14404 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14412::uu____14413 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____14438 =
                                           let uu____14444 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14444)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14438
                                     | uu____14457 -> tok_typing  in
                                   let uu____14462 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14462 with
                                    | (vars',guards',env'',decls_formals,uu____14477)
                                        ->
                                        let uu____14484 =
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
                                        (match uu____14484 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14503 ->
                                                   let uu____14507 =
                                                     let uu____14508 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14508
                                                      in
                                                   [uu____14507]
                                                in
                                             let encode_elim uu____14515 =
                                               let uu____14516 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14516 with
                                               | (head1,args) ->
                                                   let uu____14545 =
                                                     let uu____14546 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14546.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14545 with
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
                                                        let uu____14564 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14564
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
                                                                 | uu____14590
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
                                                                    let uu____14598
                                                                    =
                                                                    let uu____14599
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14599
                                                                     in
                                                                    if
                                                                    uu____14598
                                                                    then
                                                                    let uu____14606
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14606]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14608
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14621
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14621
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14643
                                                                    =
                                                                    let uu____14647
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14647
                                                                     in
                                                                    (match uu____14643
                                                                    with
                                                                    | 
                                                                    (uu____14654,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14660
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14660
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14662
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14662
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
                                                             (match uu____14608
                                                              with
                                                              | (uu____14670,arg_vars,elim_eqns_or_guards,uu____14673)
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
                                                                    let uu____14692
                                                                    =
                                                                    let uu____14696
                                                                    =
                                                                    let uu____14697
                                                                    =
                                                                    let uu____14703
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14709
                                                                    =
                                                                    let uu____14710
                                                                    =
                                                                    let uu____14713
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14713)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14710
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14703,
                                                                    uu____14709)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14697
                                                                     in
                                                                    (uu____14696,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14692
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14726
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14726,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14728
                                                                    =
                                                                    let uu____14732
                                                                    =
                                                                    let uu____14733
                                                                    =
                                                                    let uu____14739
                                                                    =
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14744
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14744]
                                                                     in
                                                                    [uu____14742]
                                                                     in
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14748
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14751,
                                                                    uu____14752)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14748
                                                                     in
                                                                    (uu____14739,
                                                                    [x],
                                                                    uu____14747)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14733
                                                                     in
                                                                    let uu____14762
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14732,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14762)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14728
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14767
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
                                                                    (let uu____14782
                                                                    =
                                                                    let uu____14783
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14783
                                                                    dapp1  in
                                                                    [uu____14782])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14767
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14787
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    let uu____14792
                                                                    =
                                                                    let uu____14798
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14804
                                                                    =
                                                                    let uu____14805
                                                                    =
                                                                    let uu____14808
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14808)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14805
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14798,
                                                                    uu____14804)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14792
                                                                     in
                                                                    (uu____14791,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14787)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14818 ->
                                                        ((let uu____14820 =
                                                            let uu____14821 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14822 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14821
                                                              uu____14822
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14820);
                                                         ([], [])))
                                                in
                                             let uu____14825 = encode_elim ()
                                                in
                                             (match uu____14825 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14837 =
                                                      let uu____14839 =
                                                        let uu____14841 =
                                                          let uu____14843 =
                                                            let uu____14845 =
                                                              let uu____14846
                                                                =
                                                                let uu____14852
                                                                  =
                                                                  let uu____14854
                                                                    =
                                                                    let uu____14855
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14855
                                                                     in
                                                                  Some
                                                                    uu____14854
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14852)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14846
                                                               in
                                                            [uu____14845]  in
                                                          let uu____14858 =
                                                            let uu____14860 =
                                                              let uu____14862
                                                                =
                                                                let uu____14864
                                                                  =
                                                                  let uu____14866
                                                                    =
                                                                    let uu____14868
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14875
                                                                    =
                                                                    let uu____14876
                                                                    =
                                                                    let uu____14882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14882)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14876
                                                                     in
                                                                    (uu____14875,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14871
                                                                     in
                                                                    let uu____14889
                                                                    =
                                                                    let uu____14891
                                                                    =
                                                                    let uu____14892
                                                                    =
                                                                    let uu____14896
                                                                    =
                                                                    let uu____14897
                                                                    =
                                                                    let uu____14903
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14909
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14903,
                                                                    uu____14909)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14897
                                                                     in
                                                                    (uu____14896,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14892
                                                                     in
                                                                    [uu____14891]
                                                                     in
                                                                    uu____14870
                                                                    ::
                                                                    uu____14889
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14868
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14866
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14864
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14862
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14860
                                                             in
                                                          FStar_List.append
                                                            uu____14843
                                                            uu____14858
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14841
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14839
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14837
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
           (fun uu____14930  ->
              fun se  ->
                match uu____14930 with
                | (g,env1) ->
                    let uu____14942 = encode_sigelt env1 se  in
                    (match uu____14942 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14978 =
        match uu____14978 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14996 ->
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
                 ((let uu____15001 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15001
                   then
                     let uu____15002 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15003 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15004 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15002 uu____15003 uu____15004
                   else ());
                  (let uu____15006 = encode_term t1 env1  in
                   match uu____15006 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15016 =
                         let uu____15020 =
                           let uu____15021 =
                             let uu____15022 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15022
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15021  in
                         new_term_constant_from_string env1 x uu____15020  in
                       (match uu____15016 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____15033 = FStar_Options.log_queries ()
                                 in
                              if uu____15033
                              then
                                let uu____15035 =
                                  let uu____15036 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15037 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15038 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15036 uu____15037 uu____15038
                                   in
                                Some uu____15035
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15049,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____15058 = encode_free_var env1 fv t t_norm []  in
                 (match uu____15058 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15077 = encode_sigelt env1 se  in
                 (match uu____15077 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15087 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15087 with | (uu____15099,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15144  ->
            match uu____15144 with
            | (l,uu____15151,uu____15152) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15173  ->
            match uu____15173 with
            | (l,uu____15181,uu____15182) ->
                let uu____15187 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____15188 =
                  let uu____15190 =
                    let uu____15191 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15191  in
                  [uu____15190]  in
                uu____15187 :: uu____15188))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15202 =
      let uu____15204 =
        let uu____15205 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15217 =
          let uu____15218 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15218 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15205;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15217
        }  in
      [uu____15204]  in
    FStar_ST.write last_env uu____15202
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15228 = FStar_ST.read last_env  in
      match uu____15228 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15234 ->
          let uu___161_15236 = e  in
          let uu____15237 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___161_15236.bindings);
            depth = (uu___161_15236.depth);
            tcenv;
            warn = (uu___161_15236.warn);
            cache = (uu___161_15236.cache);
            nolabels = (uu___161_15236.nolabels);
            use_zfuel_name = (uu___161_15236.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_15236.encode_non_total_function_typ);
            current_module_name = uu____15237
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15241 = FStar_ST.read last_env  in
    match uu____15241 with
    | [] -> failwith "Empty env stack"
    | uu____15246::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15254  ->
    let uu____15255 = FStar_ST.read last_env  in
    match uu____15255 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___162_15276 = hd1  in
          {
            bindings = (uu___162_15276.bindings);
            depth = (uu___162_15276.depth);
            tcenv = (uu___162_15276.tcenv);
            warn = (uu___162_15276.warn);
            cache = refs;
            nolabels = (uu___162_15276.nolabels);
            use_zfuel_name = (uu___162_15276.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15276.encode_non_total_function_typ);
            current_module_name = (uu___162_15276.current_module_name)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15282  ->
    let uu____15283 = FStar_ST.read last_env  in
    match uu____15283 with
    | [] -> failwith "Popping an empty stack"
    | uu____15288::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15296  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15299  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15302  ->
    let uu____15303 = FStar_ST.read last_env  in
    match uu____15303 with
    | hd1::uu____15309::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15315 -> failwith "Impossible"
  
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
        let uu____15360 = FStar_Options.log_queries ()  in
        if uu____15360
        then
          let uu____15362 =
            let uu____15363 =
              let uu____15364 =
                let uu____15365 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15365 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15364  in
            FStar_SMTEncoding_Term.Caption uu____15363  in
          uu____15362 :: decls
        else decls  in
      let env =
        let uu____15372 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____15372 tcenv  in
      let uu____15373 = encode_sigelt env se  in
      match uu____15373 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15379 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15379))
  
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
      (let uu____15390 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15390
       then
         let uu____15391 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15391
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let uu____15396 =
         encode_signature
           (let uu___163_15400 = env  in
            {
              bindings = (uu___163_15400.bindings);
              depth = (uu___163_15400.depth);
              tcenv = (uu___163_15400.tcenv);
              warn = false;
              cache = (uu___163_15400.cache);
              nolabels = (uu___163_15400.nolabels);
              use_zfuel_name = (uu___163_15400.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15400.encode_non_total_function_typ);
              current_module_name = (uu___163_15400.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15396 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15412 = FStar_Options.log_queries ()  in
             if uu____15412
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___164_15417 = env1  in
               {
                 bindings = (uu___164_15417.bindings);
                 depth = (uu___164_15417.depth);
                 tcenv = (uu___164_15417.tcenv);
                 warn = true;
                 cache = (uu___164_15417.cache);
                 nolabels = (uu___164_15417.nolabels);
                 use_zfuel_name = (uu___164_15417.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15417.encode_non_total_function_typ);
                 current_module_name = (uu___164_15417.current_module_name)
               });
            (let uu____15419 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15419
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
        (let uu____15454 =
           let uu____15455 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15455.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15454);
        (let env =
           let uu____15457 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____15457 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15464 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15485 = aux rest  in
                 (match uu____15485 with
                  | (out,rest1) ->
                      let t =
                        let uu____15503 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____15503 with
                        | Some uu____15507 ->
                            let uu____15508 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____15508
                              x.FStar_Syntax_Syntax.sort
                        | uu____15509 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____15512 =
                        let uu____15514 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15515 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15515.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15515.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____15514 :: out  in
                      (uu____15512, rest1))
             | uu____15518 -> ([], bindings1)  in
           let uu____15522 = aux bindings  in
           match uu____15522 with
           | (closing,bindings1) ->
               let uu____15536 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____15536, bindings1)
            in
         match uu____15464 with
         | (q1,bindings1) ->
             let uu____15549 =
               let uu____15552 =
                 FStar_List.filter
                   (fun uu___134_15554  ->
                      match uu___134_15554 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15555 ->
                          false
                      | uu____15559 -> true) bindings1
                  in
               encode_env_bindings env uu____15552  in
             (match uu____15549 with
              | (env_decls,env1) ->
                  ((let uu____15570 =
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
                    if uu____15570
                    then
                      let uu____15571 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15571
                    else ());
                   (let uu____15573 = encode_formula q1 env1  in
                    match uu____15573 with
                    | (phi,qdecls) ->
                        let uu____15585 =
                          let uu____15588 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15588 phi
                           in
                        (match uu____15585 with
                         | (labels,phi1) ->
                             let uu____15598 = encode_labels labels  in
                             (match uu____15598 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15619 =
                                      let uu____15623 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15624 =
                                        varops.mk_unique "@query"  in
                                      (uu____15623, (Some "query"),
                                        uu____15624)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15619
                                     in
                                  let suffix =
                                    let uu____15628 =
                                      let uu____15630 =
                                        let uu____15632 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15632
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15630
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15628
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15644 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____15644 tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15646 = encode_formula q env  in
       match uu____15646 with
       | (f,uu____15650) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15652) -> true
             | uu____15655 -> false)))
  