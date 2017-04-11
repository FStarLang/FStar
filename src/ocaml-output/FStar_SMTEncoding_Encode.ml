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
                                      let uu____4199 =
                                        let uu____4204 = codomain_eff lc2  in
                                        match uu____4204 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c
                                               in
                                            let uu____4216 =
                                              encode_term tfun env  in
                                            (match uu____4216 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1))
                                         in
                                      (match uu____4199 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4235 =
                                               let uu____4241 =
                                                 let uu____4242 =
                                                   let uu____4245 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards
                                                      in
                                                   (uu____4245, body3)  in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4242
                                                  in
                                               ([], vars, uu____4241)  in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4235
                                              in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body
                                              in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4253 =
                                                   let uu____4255 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1
                                                      in
                                                   FStar_List.append
                                                     uu____4255 cvars
                                                    in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4253
                                              in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body)
                                              in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey
                                              in
                                           let uu____4266 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash
                                              in
                                           (match uu____4266 with
                                            | Some (t1,uu____4281,uu____4282)
                                                ->
                                                let uu____4292 =
                                                  let uu____4293 =
                                                    let uu____4297 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (t1, uu____4297)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4293
                                                   in
                                                (uu____4292, [])
                                            | None  ->
                                                let uu____4308 =
                                                  is_eta env vars body3  in
                                                (match uu____4308 with
                                                 | Some t1 -> (t1, [])
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1
                                                        in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name
                                                          in
                                                       let fsym =
                                                         let uu____4321 =
                                                           let uu____4322 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4322
                                                            in
                                                         varops.mk_unique
                                                           uu____4321
                                                          in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym)
                                                        in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None)
                                                        in
                                                     let f =
                                                       let uu____4327 =
                                                         let uu____4331 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____4331)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4327
                                                        in
                                                     let app =
                                                       mk_Apply f vars  in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1
                                                              in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym
                                                              in
                                                           let uu____4343 =
                                                             let uu____4344 =
                                                               let uu____4348
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____4348,
                                                                 (Some a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____4344
                                                              in
                                                           [uu____4343]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____4356 =
                                                         let uu____4360 =
                                                           let uu____4361 =
                                                             let uu____4367 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4367)
                                                              in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4361
                                                            in
                                                         (uu____4360,
                                                           (Some a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Term.Assume
                                                         uu____4356
                                                        in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f])))
                                                        in
                                                     (FStar_Util.smap_add
                                                        env.cache tkey_hash
                                                        (fsym, cvar_sorts,
                                                          f_decls);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4385,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4386;
                          FStar_Syntax_Syntax.lbunivs = uu____4387;
                          FStar_Syntax_Syntax.lbtyp = uu____4388;
                          FStar_Syntax_Syntax.lbeff = uu____4389;
                          FStar_Syntax_Syntax.lbdef = uu____4390;_}::uu____4391),uu____4392)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4410;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4412;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4428 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4441 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4441, [decl_e])))
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
              let uu____4483 = encode_term e1 env  in
              match uu____4483 with
              | (ee1,decls1) ->
                  let uu____4490 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4490 with
                   | (xs,e21) ->
                       let uu____4504 = FStar_List.hd xs  in
                       (match uu____4504 with
                        | (x1,uu____4512) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4514 = encode_body e21 env'  in
                            (match uu____4514 with
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
            let uu____4536 =
              let uu____4540 =
                let uu____4541 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4541  in
              gen_term_var env uu____4540  in
            match uu____4536 with
            | (scrsym,scr',env1) ->
                let uu____4555 = encode_term e env1  in
                (match uu____4555 with
                 | (scr,decls) ->
                     let uu____4562 =
                       let encode_branch b uu____4578 =
                         match uu____4578 with
                         | (else_case,decls1) ->
                             let uu____4589 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4589 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p  in
                                  FStar_List.fold_right
                                    (fun uu____4619  ->
                                       fun uu____4620  ->
                                         match (uu____4619, uu____4620) with
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
                                                       fun uu____4657  ->
                                                         match uu____4657
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1)
                                                in
                                             let uu____4662 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4677 =
                                                     encode_term w1 env2  in
                                                   (match uu____4677 with
                                                    | (w2,decls21) ->
                                                        let uu____4685 =
                                                          let uu____4686 =
                                                            let uu____4689 =
                                                              let uu____4690
                                                                =
                                                                let uu____4693
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4693)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4690
                                                               in
                                                            (guard,
                                                              uu____4689)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4686
                                                           in
                                                        (uu____4685, decls21))
                                                in
                                             (match uu____4662 with
                                              | (guard1,decls21) ->
                                                  let uu____4701 =
                                                    encode_br br env2  in
                                                  (match uu____4701 with
                                                   | (br1,decls3) ->
                                                       let uu____4709 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4709,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4562 with
                      | (match_tm,decls1) ->
                          let uu____4721 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4721, decls1)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4752 ->
          let uu____4753 = encode_one_pat env pat  in [uu____4753]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4765 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4765
       then
         let uu____4766 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4766
       else ());
      (let uu____4768 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4768 with
       | (vars,pat_term) ->
           let uu____4778 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4801  ->
                     fun v1  ->
                       match uu____4801 with
                       | (env1,vars1) ->
                           let uu____4829 = gen_term_var env1 v1  in
                           (match uu____4829 with
                            | (xx,uu____4841,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4778 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4888 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4896 =
                        let uu____4899 = encode_const c  in
                        (scrutinee, uu____4899)  in
                      FStar_SMTEncoding_Util.mkEq uu____4896
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4918 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____4918 with
                        | (uu____4922,uu____4923::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4925 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4946  ->
                                  match uu____4946 with
                                  | (arg,uu____4952) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4962 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4962))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4981 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4996 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5011 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5033  ->
                                  match uu____5033 with
                                  | (arg,uu____5042) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5052 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____5052))
                         in
                      FStar_All.pipe_right uu____5011 FStar_List.flatten
                   in
                let pat_term1 uu____5068 = encode_term pat_term env1  in
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
      let uu____5075 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5090  ->
                fun uu____5091  ->
                  match (uu____5090, uu____5091) with
                  | ((tms,decls),(t,uu____5111)) ->
                      let uu____5122 = encode_term t env  in
                      (match uu____5122 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5075 with | (l1,decls) -> ((FStar_List.rev l1), decls)

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
            let uu____5160 = FStar_Syntax_Util.list_elements e  in
            match uu____5160 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____5178 =
              let uu____5188 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____5188 FStar_Syntax_Util.head_and_args
               in
            match uu____5178 with
            | (head1,args) ->
                let uu____5219 =
                  let uu____5227 =
                    let uu____5228 = FStar_Syntax_Util.un_uinst head1  in
                    uu____5228.FStar_Syntax_Syntax.n  in
                  (uu____5227, args)  in
                (match uu____5219 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5242,uu____5243)::(e,uu____5245)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5276)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5297 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____5330 =
                let uu____5340 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____5340
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____5330 with
              | (head1,args) ->
                  let uu____5369 =
                    let uu____5377 =
                      let uu____5378 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5378.FStar_Syntax_Syntax.n  in
                    (uu____5377, args)  in
                  (match uu____5369 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5391)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5411 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5429 = smt_pat_or t1  in
                (match uu____5429 with
                 | Some e ->
                     let uu____5445 = list_elements1 e  in
                     FStar_All.pipe_right uu____5445
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5462 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5462
                               (FStar_List.map one_pat)))
                 | uu____5476 ->
                     let uu____5480 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5480])
            | uu____5511 ->
                let uu____5513 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5513]
             in
          let uu____5544 =
            let uu____5560 =
              let uu____5561 = FStar_Syntax_Subst.compress t  in
              uu____5561.FStar_Syntax_Syntax.n  in
            match uu____5560 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5591 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5591 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5626;
                            FStar_Syntax_Syntax.effect_name = uu____5627;
                            FStar_Syntax_Syntax.result_typ = uu____5628;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5630)::(post,uu____5632)::(pats,uu____5634)::[];
                            FStar_Syntax_Syntax.flags = uu____5635;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5669 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5669)
                      | uu____5688 -> failwith "impos"))
            | uu____5704 -> failwith "Impos"  in
          match uu____5544 with
          | (binders,pre,post,patterns) ->
              let uu____5748 = encode_binders None binders env  in
              (match uu____5748 with
               | (vars,guards,env1,decls,uu____5763) ->
                   let uu____5770 =
                     let uu____5777 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5808 =
                                 let uu____5813 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5829  ->
                                           match uu____5829 with
                                           | (t1,uu____5836) ->
                                               encode_term t1
                                                 (let uu___146_5839 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___146_5839.bindings);
                                                    depth =
                                                      (uu___146_5839.depth);
                                                    tcenv =
                                                      (uu___146_5839.tcenv);
                                                    warn =
                                                      (uu___146_5839.warn);
                                                    cache =
                                                      (uu___146_5839.cache);
                                                    nolabels =
                                                      (uu___146_5839.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___146_5839.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___146_5839.current_module_name)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5813
                                   FStar_List.unzip
                                  in
                               match uu____5808 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5777 FStar_List.unzip  in
                   (match uu____5770 with
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
                                           let uu____5903 =
                                             let uu____5904 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5904 e
                                              in
                                           uu____5903 :: p))
                               | uu____5905 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5934 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5934 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5942 =
                                           let uu____5943 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5943 tl1
                                            in
                                         aux uu____5942 vars2
                                     | uu____5944 -> pats  in
                                   let uu____5948 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5948 vars)
                           in
                        let env2 =
                          let uu___147_5950 = env1  in
                          {
                            bindings = (uu___147_5950.bindings);
                            depth = (uu___147_5950.depth);
                            tcenv = (uu___147_5950.tcenv);
                            warn = (uu___147_5950.warn);
                            cache = (uu___147_5950.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5950.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___147_5950.encode_non_total_function_typ);
                            current_module_name =
                              (uu___147_5950.current_module_name)
                          }  in
                        let uu____5951 =
                          let uu____5954 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5954 env2  in
                        (match uu____5951 with
                         | (pre1,decls'') ->
                             let uu____5959 =
                               let uu____5962 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5962 env2  in
                             (match uu____5959 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5969 =
                                    let uu____5970 =
                                      let uu____5976 =
                                        let uu____5977 =
                                          let uu____5980 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5980, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5977
                                         in
                                      (pats1, vars, uu____5976)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5970
                                     in
                                  (uu____5969, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5993 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5993
        then
          let uu____5994 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5995 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5994 uu____5995
        else ()  in
      let enc f r l =
        let uu____6022 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6035 = encode_term (Prims.fst x) env  in
                 match uu____6035 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____6022 with
        | (decls,args) ->
            let uu____6052 =
              let uu___148_6053 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6053.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6053.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6052, decls)
         in
      let const_op f r uu____6072 = let uu____6075 = f r  in (uu____6075, [])
         in
      let un_op f l =
        let uu____6091 = FStar_List.hd l  in FStar_All.pipe_left f uu____6091
         in
      let bin_op f uu___120_6104 =
        match uu___120_6104 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6112 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6139 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6148  ->
                 match uu____6148 with
                 | (t,uu____6156) ->
                     let uu____6157 = encode_formula t env  in
                     (match uu____6157 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6139 with
        | (decls,phis) ->
            let uu____6174 =
              let uu___149_6175 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6175.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6175.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6174, decls)
         in
      let eq_op r uu___121_6191 =
        match uu___121_6191 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6251 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6251 r [e1; e2]
        | l ->
            let uu____6271 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6271 r l
         in
      let mk_imp1 r uu___122_6290 =
        match uu___122_6290 with
        | (lhs,uu____6294)::(rhs,uu____6296)::[] ->
            let uu____6317 = encode_formula rhs env  in
            (match uu____6317 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6326) ->
                      (l1, decls1)
                  | uu____6329 ->
                      let uu____6330 = encode_formula lhs env  in
                      (match uu____6330 with
                       | (l2,decls2) ->
                           let uu____6337 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6337, (FStar_List.append decls1 decls2)))))
        | uu____6339 -> failwith "impossible"  in
      let mk_ite r uu___123_6354 =
        match uu___123_6354 with
        | (guard,uu____6358)::(_then,uu____6360)::(_else,uu____6362)::[] ->
            let uu____6391 = encode_formula guard env  in
            (match uu____6391 with
             | (g,decls1) ->
                 let uu____6398 = encode_formula _then env  in
                 (match uu____6398 with
                  | (t,decls2) ->
                      let uu____6405 = encode_formula _else env  in
                      (match uu____6405 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6414 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6433 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6433  in
      let connectives =
        let uu____6445 =
          let uu____6454 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6454)  in
        let uu____6467 =
          let uu____6477 =
            let uu____6486 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6486)  in
          let uu____6499 =
            let uu____6509 =
              let uu____6519 =
                let uu____6528 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6528)  in
              let uu____6541 =
                let uu____6551 =
                  let uu____6561 =
                    let uu____6570 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6570)  in
                  [uu____6561;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6551  in
              uu____6519 :: uu____6541  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6509  in
          uu____6477 :: uu____6499  in
        uu____6445 :: uu____6467  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6732 = encode_formula phi' env  in
            (match uu____6732 with
             | (phi2,decls) ->
                 let uu____6739 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6739, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6740 ->
            let uu____6745 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6745 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6774 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6774 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6782;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6784;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6800 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6800 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6832::(x,uu____6834)::(t,uu____6836)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6870 = encode_term x env  in
                 (match uu____6870 with
                  | (x1,decls) ->
                      let uu____6877 = encode_term t env  in
                      (match uu____6877 with
                       | (t1,decls') ->
                           let uu____6884 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6884, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6888)::(msg,uu____6890)::(phi2,uu____6892)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6926 =
                   let uu____6929 =
                     let uu____6930 = FStar_Syntax_Subst.compress r  in
                     uu____6930.FStar_Syntax_Syntax.n  in
                   let uu____6933 =
                     let uu____6934 = FStar_Syntax_Subst.compress msg  in
                     uu____6934.FStar_Syntax_Syntax.n  in
                   (uu____6929, uu____6933)  in
                 (match uu____6926 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6941))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6957 -> fallback phi2)
             | uu____6960 when head_redex env head2 ->
                 let uu____6968 = whnf env phi1  in
                 encode_formula uu____6968 env
             | uu____6969 ->
                 let uu____6977 = encode_term phi1 env  in
                 (match uu____6977 with
                  | (tt,decls) ->
                      let uu____6984 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___150_6985 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6985.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6985.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6984, decls)))
        | uu____6988 ->
            let uu____6989 = encode_term phi1 env  in
            (match uu____6989 with
             | (tt,decls) ->
                 let uu____6996 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___151_6997 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6997.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6997.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6996, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____7024 = encode_binders None bs env1  in
        match uu____7024 with
        | (vars,guards,env2,decls,uu____7046) ->
            let uu____7053 =
              let uu____7060 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7083 =
                          let uu____7088 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7102  ->
                                    match uu____7102 with
                                    | (t,uu____7108) ->
                                        encode_term t
                                          (let uu___152_7109 = env2  in
                                           {
                                             bindings =
                                               (uu___152_7109.bindings);
                                             depth = (uu___152_7109.depth);
                                             tcenv = (uu___152_7109.tcenv);
                                             warn = (uu___152_7109.warn);
                                             cache = (uu___152_7109.cache);
                                             nolabels =
                                               (uu___152_7109.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___152_7109.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___152_7109.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____7088 FStar_List.unzip
                           in
                        match uu____7083 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7060 FStar_List.unzip  in
            (match uu____7053 with
             | (pats,decls') ->
                 let uu____7161 = encode_formula body env2  in
                 (match uu____7161 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7180;
                             FStar_SMTEncoding_Term.rng = uu____7181;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7189 -> guards  in
                      let uu____7192 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7192, body1,
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
                (fun uu____7226  ->
                   match uu____7226 with
                   | (x,uu____7230) ->
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
               let uu____7236 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7242 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7242) uu____7236 tl1
                in
             let uu____7244 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7256  ->
                       match uu____7256 with
                       | (b,uu____7260) ->
                           let uu____7261 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7261))
                in
             (match uu____7244 with
              | None  -> ()
              | Some (x,uu____7265) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7275 =
                    let uu____7276 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7276
                     in
                  FStar_Errors.warn pos uu____7275)
          in
       let uu____7277 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7277 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7283 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7319  ->
                     match uu____7319 with
                     | (l,uu____7329) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7283 with
            | None  -> fallback phi1
            | Some (uu____7352,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7381 = encode_q_body env vars pats body  in
             match uu____7381 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7407 =
                     let uu____7413 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7413)  in
                   FStar_SMTEncoding_Term.mkForall uu____7407
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7425 = encode_q_body env vars pats body  in
             match uu____7425 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7450 =
                   let uu____7451 =
                     let uu____7457 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7457)  in
                   FStar_SMTEncoding_Term.mkExists uu____7451
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7450, decls))))

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
  let uu____7506 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7506 with
  | (asym,a) ->
      let uu____7511 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7511 with
       | (xsym,x) ->
           let uu____7516 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7516 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7546 =
                      let uu____7552 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7552, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7546  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7567 =
                      let uu____7571 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7571)  in
                    FStar_SMTEncoding_Util.mkApp uu____7567  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7579 =
                    let uu____7581 =
                      let uu____7583 =
                        let uu____7585 =
                          let uu____7586 =
                            let uu____7590 =
                              let uu____7591 =
                                let uu____7597 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7597)  in
                              FStar_SMTEncoding_Util.mkForall uu____7591  in
                            (uu____7590, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7586  in
                        let uu____7606 =
                          let uu____7608 =
                            let uu____7609 =
                              let uu____7613 =
                                let uu____7614 =
                                  let uu____7620 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7620)  in
                                FStar_SMTEncoding_Util.mkForall uu____7614
                                 in
                              (uu____7613,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7609  in
                          [uu____7608]  in
                        uu____7585 :: uu____7606  in
                      xtok_decl :: uu____7583  in
                    xname_decl :: uu____7581  in
                  (xtok1, uu____7579)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7669 =
                    let uu____7677 =
                      let uu____7683 =
                        let uu____7684 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7684
                         in
                      quant axy uu____7683  in
                    (FStar_Syntax_Const.op_Eq, uu____7677)  in
                  let uu____7690 =
                    let uu____7699 =
                      let uu____7707 =
                        let uu____7713 =
                          let uu____7714 =
                            let uu____7715 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7715  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7714
                           in
                        quant axy uu____7713  in
                      (FStar_Syntax_Const.op_notEq, uu____7707)  in
                    let uu____7721 =
                      let uu____7730 =
                        let uu____7738 =
                          let uu____7744 =
                            let uu____7745 =
                              let uu____7746 =
                                let uu____7749 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7750 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7749, uu____7750)  in
                              FStar_SMTEncoding_Util.mkLT uu____7746  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7745
                             in
                          quant xy uu____7744  in
                        (FStar_Syntax_Const.op_LT, uu____7738)  in
                      let uu____7756 =
                        let uu____7765 =
                          let uu____7773 =
                            let uu____7779 =
                              let uu____7780 =
                                let uu____7781 =
                                  let uu____7784 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7785 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7784, uu____7785)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7781  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7780
                               in
                            quant xy uu____7779  in
                          (FStar_Syntax_Const.op_LTE, uu____7773)  in
                        let uu____7791 =
                          let uu____7800 =
                            let uu____7808 =
                              let uu____7814 =
                                let uu____7815 =
                                  let uu____7816 =
                                    let uu____7819 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7820 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7819, uu____7820)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7816  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7815
                                 in
                              quant xy uu____7814  in
                            (FStar_Syntax_Const.op_GT, uu____7808)  in
                          let uu____7826 =
                            let uu____7835 =
                              let uu____7843 =
                                let uu____7849 =
                                  let uu____7850 =
                                    let uu____7851 =
                                      let uu____7854 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7855 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7854, uu____7855)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7851
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7850
                                   in
                                quant xy uu____7849  in
                              (FStar_Syntax_Const.op_GTE, uu____7843)  in
                            let uu____7861 =
                              let uu____7870 =
                                let uu____7878 =
                                  let uu____7884 =
                                    let uu____7885 =
                                      let uu____7886 =
                                        let uu____7889 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7890 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7889, uu____7890)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7886
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7885
                                     in
                                  quant xy uu____7884  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7878)
                                 in
                              let uu____7896 =
                                let uu____7905 =
                                  let uu____7913 =
                                    let uu____7919 =
                                      let uu____7920 =
                                        let uu____7921 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7921
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7920
                                       in
                                    quant qx uu____7919  in
                                  (FStar_Syntax_Const.op_Minus, uu____7913)
                                   in
                                let uu____7927 =
                                  let uu____7936 =
                                    let uu____7944 =
                                      let uu____7950 =
                                        let uu____7951 =
                                          let uu____7952 =
                                            let uu____7955 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7956 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7955, uu____7956)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7952
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7951
                                         in
                                      quant xy uu____7950  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7944)
                                     in
                                  let uu____7962 =
                                    let uu____7971 =
                                      let uu____7979 =
                                        let uu____7985 =
                                          let uu____7986 =
                                            let uu____7987 =
                                              let uu____7990 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7991 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7990, uu____7991)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7987
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7986
                                           in
                                        quant xy uu____7985  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7979)
                                       in
                                    let uu____7997 =
                                      let uu____8006 =
                                        let uu____8014 =
                                          let uu____8020 =
                                            let uu____8021 =
                                              let uu____8022 =
                                                let uu____8025 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____8026 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____8025, uu____8026)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8022
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8021
                                             in
                                          quant xy uu____8020  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8014)
                                         in
                                      let uu____8032 =
                                        let uu____8041 =
                                          let uu____8049 =
                                            let uu____8055 =
                                              let uu____8056 =
                                                let uu____8057 =
                                                  let uu____8060 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8061 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8060, uu____8061)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8057
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8056
                                               in
                                            quant xy uu____8055  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8049)
                                           in
                                        let uu____8067 =
                                          let uu____8076 =
                                            let uu____8084 =
                                              let uu____8090 =
                                                let uu____8091 =
                                                  let uu____8092 =
                                                    let uu____8095 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8096 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8095, uu____8096)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8092
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8091
                                                 in
                                              quant xy uu____8090  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8084)
                                             in
                                          let uu____8102 =
                                            let uu____8111 =
                                              let uu____8119 =
                                                let uu____8125 =
                                                  let uu____8126 =
                                                    let uu____8127 =
                                                      let uu____8130 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8131 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8130,
                                                        uu____8131)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8127
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8126
                                                   in
                                                quant xy uu____8125  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8119)
                                               in
                                            let uu____8137 =
                                              let uu____8146 =
                                                let uu____8154 =
                                                  let uu____8160 =
                                                    let uu____8161 =
                                                      let uu____8162 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8162
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8161
                                                     in
                                                  quant qx uu____8160  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8154)
                                                 in
                                              [uu____8146]  in
                                            uu____8111 :: uu____8137  in
                                          uu____8076 :: uu____8102  in
                                        uu____8041 :: uu____8067  in
                                      uu____8006 :: uu____8032  in
                                    uu____7971 :: uu____7997  in
                                  uu____7936 :: uu____7962  in
                                uu____7905 :: uu____7927  in
                              uu____7870 :: uu____7896  in
                            uu____7835 :: uu____7861  in
                          uu____7800 :: uu____7826  in
                        uu____7765 :: uu____7791  in
                      uu____7730 :: uu____7756  in
                    uu____7699 :: uu____7721  in
                  uu____7669 :: uu____7690  in
                let mk1 l v1 =
                  let uu____8290 =
                    let uu____8295 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8327  ->
                              match uu____8327 with
                              | (l',uu____8336) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8295
                      (FStar_Option.map
                         (fun uu____8369  ->
                            match uu____8369 with | (uu____8380,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8290 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8421  ->
                          match uu____8421 with
                          | (l',uu____8430) -> FStar_Ident.lid_equals l l'))
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
        let uu____8456 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____8456 with
        | (xxsym,xx) ->
            let uu____8461 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____8461 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____8469 =
                   let uu____8473 =
                     let uu____8474 =
                       let uu____8480 =
                         let uu____8481 =
                           let uu____8484 =
                             let uu____8485 =
                               let uu____8488 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____8488)  in
                             FStar_SMTEncoding_Util.mkEq uu____8485  in
                           (xx_has_type, uu____8484)  in
                         FStar_SMTEncoding_Util.mkImp uu____8481  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8480)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____8474  in
                   let uu____8501 =
                     let uu____8502 =
                       let uu____8503 =
                         let uu____8504 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____8504  in
                       Prims.strcat module_name uu____8503  in
                     varops.mk_unique uu____8502  in
                   (uu____8473, (Some "pretyping"), uu____8501)  in
                 FStar_SMTEncoding_Term.Assume uu____8469)
  
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
    let uu____8534 =
      let uu____8535 =
        let uu____8539 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8539, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8535  in
    let uu____8541 =
      let uu____8543 =
        let uu____8544 =
          let uu____8548 =
            let uu____8549 =
              let uu____8555 =
                let uu____8556 =
                  let uu____8559 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8559)  in
                FStar_SMTEncoding_Util.mkImp uu____8556  in
              ([[typing_pred]], [xx], uu____8555)  in
            mkForall_fuel uu____8549  in
          (uu____8548, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8544  in
      [uu____8543]  in
    uu____8534 :: uu____8541  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8587 =
      let uu____8588 =
        let uu____8592 =
          let uu____8593 =
            let uu____8599 =
              let uu____8602 =
                let uu____8604 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8604]  in
              [uu____8602]  in
            let uu____8607 =
              let uu____8608 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8608 tt  in
            (uu____8599, [bb], uu____8607)  in
          FStar_SMTEncoding_Util.mkForall uu____8593  in
        (uu____8592, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8588  in
    let uu____8619 =
      let uu____8621 =
        let uu____8622 =
          let uu____8626 =
            let uu____8627 =
              let uu____8633 =
                let uu____8634 =
                  let uu____8637 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8637)  in
                FStar_SMTEncoding_Util.mkImp uu____8634  in
              ([[typing_pred]], [xx], uu____8633)  in
            mkForall_fuel uu____8627  in
          (uu____8626, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8622  in
      [uu____8621]  in
    uu____8587 :: uu____8619  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8671 =
        let uu____8672 =
          let uu____8676 =
            let uu____8678 =
              let uu____8680 =
                let uu____8682 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8683 =
                  let uu____8685 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8685]  in
                uu____8682 :: uu____8683  in
              tt :: uu____8680  in
            tt :: uu____8678  in
          ("Prims.Precedes", uu____8676)  in
        FStar_SMTEncoding_Util.mkApp uu____8672  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8671  in
    let precedes_y_x =
      let uu____8688 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8688  in
    let uu____8690 =
      let uu____8691 =
        let uu____8695 =
          let uu____8696 =
            let uu____8702 =
              let uu____8705 =
                let uu____8707 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8707]  in
              [uu____8705]  in
            let uu____8710 =
              let uu____8711 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8711 tt  in
            (uu____8702, [bb], uu____8710)  in
          FStar_SMTEncoding_Util.mkForall uu____8696  in
        (uu____8695, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8691  in
    let uu____8722 =
      let uu____8724 =
        let uu____8725 =
          let uu____8729 =
            let uu____8730 =
              let uu____8736 =
                let uu____8737 =
                  let uu____8740 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8740)  in
                FStar_SMTEncoding_Util.mkImp uu____8737  in
              ([[typing_pred]], [xx], uu____8736)  in
            mkForall_fuel uu____8730  in
          (uu____8729, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8725  in
      let uu____8753 =
        let uu____8755 =
          let uu____8756 =
            let uu____8760 =
              let uu____8761 =
                let uu____8767 =
                  let uu____8768 =
                    let uu____8771 =
                      let uu____8772 =
                        let uu____8774 =
                          let uu____8776 =
                            let uu____8778 =
                              let uu____8779 =
                                let uu____8782 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8783 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8782, uu____8783)  in
                              FStar_SMTEncoding_Util.mkGT uu____8779  in
                            let uu____8784 =
                              let uu____8786 =
                                let uu____8787 =
                                  let uu____8790 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8791 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8790, uu____8791)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8787  in
                              let uu____8792 =
                                let uu____8794 =
                                  let uu____8795 =
                                    let uu____8798 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8799 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8798, uu____8799)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8795  in
                                [uu____8794]  in
                              uu____8786 :: uu____8792  in
                            uu____8778 :: uu____8784  in
                          typing_pred_y :: uu____8776  in
                        typing_pred :: uu____8774  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8772  in
                    (uu____8771, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8768  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8767)
                 in
              mkForall_fuel uu____8761  in
            (uu____8760, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Term.Assume uu____8756  in
        [uu____8755]  in
      uu____8724 :: uu____8753  in
    uu____8690 :: uu____8722  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8829 =
      let uu____8830 =
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
        (uu____8834, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Term.Assume uu____8830  in
    let uu____8861 =
      let uu____8863 =
        let uu____8864 =
          let uu____8868 =
            let uu____8869 =
              let uu____8875 =
                let uu____8876 =
                  let uu____8879 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8879)  in
                FStar_SMTEncoding_Util.mkImp uu____8876  in
              ([[typing_pred]], [xx], uu____8875)  in
            mkForall_fuel uu____8869  in
          (uu____8868, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Term.Assume uu____8864  in
      [uu____8863]  in
    uu____8829 :: uu____8861  in
  let mk_ref1 env reft_name uu____8901 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8912 =
        let uu____8916 =
          let uu____8918 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8918]
           in
        (reft_name, uu____8916)  in
      FStar_SMTEncoding_Util.mkApp uu____8912  in
    let refb =
      let uu____8921 =
        let uu____8925 =
          let uu____8927 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8927]
           in
        (reft_name, uu____8925)  in
      FStar_SMTEncoding_Util.mkApp uu____8921  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8931 =
      let uu____8932 =
        let uu____8936 =
          let uu____8937 =
            let uu____8943 =
              let uu____8944 =
                let uu____8947 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8947)  in
              FStar_SMTEncoding_Util.mkImp uu____8944  in
            ([[typing_pred]], [xx; aa], uu____8943)  in
          mkForall_fuel uu____8937  in
        (uu____8936, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Term.Assume uu____8932  in
    let uu____8962 =
      let uu____8964 =
        let uu____8965 =
          let uu____8969 =
            let uu____8970 =
              let uu____8976 =
                let uu____8977 =
                  let uu____8980 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8981 =
                    let uu____8982 =
                      let uu____8985 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8986 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8985, uu____8986)  in
                    FStar_SMTEncoding_Util.mkEq uu____8982  in
                  (uu____8980, uu____8981)  in
                FStar_SMTEncoding_Util.mkImp uu____8977  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8976)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8970  in
          (uu____8969, (Some "ref typing is injective"), "ref_injectivity")
           in
        FStar_SMTEncoding_Term.Assume uu____8965  in
      [uu____8964]  in
    uu____8931 :: uu____8962  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____9028 =
      let uu____9029 =
        let uu____9033 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9033, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Term.Assume uu____9029  in
    [uu____9028]  in
  let mk_and_interp env conj uu____9044 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9054 =
        let uu____9058 =
          let uu____9060 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____9060]  in
        ("Valid", uu____9058)  in
      FStar_SMTEncoding_Util.mkApp uu____9054  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9067 =
      let uu____9068 =
        let uu____9072 =
          let uu____9073 =
            let uu____9079 =
              let uu____9080 =
                let uu____9083 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9083, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9080  in
            ([[valid]], [aa; bb], uu____9079)  in
          FStar_SMTEncoding_Util.mkForall uu____9073  in
        (uu____9072, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9068  in
    [uu____9067]  in
  let mk_or_interp env disj uu____9107 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9117 =
        let uu____9121 =
          let uu____9123 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____9123]  in
        ("Valid", uu____9121)  in
      FStar_SMTEncoding_Util.mkApp uu____9117  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9130 =
      let uu____9131 =
        let uu____9135 =
          let uu____9136 =
            let uu____9142 =
              let uu____9143 =
                let uu____9146 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9146, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9143  in
            ([[valid]], [aa; bb], uu____9142)  in
          FStar_SMTEncoding_Util.mkForall uu____9136  in
        (uu____9135, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9131  in
    [uu____9130]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____9184 =
        let uu____9188 =
          let uu____9190 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____9190]  in
        ("Valid", uu____9188)  in
      FStar_SMTEncoding_Util.mkApp uu____9184  in
    let uu____9193 =
      let uu____9194 =
        let uu____9198 =
          let uu____9199 =
            let uu____9205 =
              let uu____9206 =
                let uu____9209 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9209, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9206  in
            ([[valid]], [aa; xx1; yy1], uu____9205)  in
          FStar_SMTEncoding_Util.mkForall uu____9199  in
        (uu____9198, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9194  in
    [uu____9193]  in
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
      let uu____9253 =
        let uu____9257 =
          let uu____9259 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____9259]  in
        ("Valid", uu____9257)  in
      FStar_SMTEncoding_Util.mkApp uu____9253  in
    let uu____9262 =
      let uu____9263 =
        let uu____9267 =
          let uu____9268 =
            let uu____9274 =
              let uu____9275 =
                let uu____9278 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9278, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9275  in
            ([[valid]], [aa; bb; xx1; yy1], uu____9274)  in
          FStar_SMTEncoding_Util.mkForall uu____9268  in
        (uu____9267, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9263  in
    [uu____9262]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9316 =
        let uu____9320 =
          let uu____9322 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____9322]  in
        ("Valid", uu____9320)  in
      FStar_SMTEncoding_Util.mkApp uu____9316  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9329 =
      let uu____9330 =
        let uu____9334 =
          let uu____9335 =
            let uu____9341 =
              let uu____9342 =
                let uu____9345 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9345, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9342  in
            ([[valid]], [aa; bb], uu____9341)  in
          FStar_SMTEncoding_Util.mkForall uu____9335  in
        (uu____9334, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9330  in
    [uu____9329]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9379 =
        let uu____9383 =
          let uu____9385 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9385]  in
        ("Valid", uu____9383)  in
      FStar_SMTEncoding_Util.mkApp uu____9379  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9392 =
      let uu____9393 =
        let uu____9397 =
          let uu____9398 =
            let uu____9404 =
              let uu____9405 =
                let uu____9408 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9408, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9405  in
            ([[valid]], [aa; bb], uu____9404)  in
          FStar_SMTEncoding_Util.mkForall uu____9398  in
        (uu____9397, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9393  in
    [uu____9392]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9438 =
        let uu____9442 =
          let uu____9444 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9444]  in
        ("Valid", uu____9442)  in
      FStar_SMTEncoding_Util.mkApp uu____9438  in
    let not_valid_a =
      let uu____9448 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9448  in
    let uu____9450 =
      let uu____9451 =
        let uu____9455 =
          let uu____9456 =
            let uu____9462 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9462)  in
          FStar_SMTEncoding_Util.mkForall uu____9456  in
        (uu____9455, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9451  in
    [uu____9450]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9498 =
        let uu____9502 =
          let uu____9504 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9504]  in
        ("Valid", uu____9502)  in
      FStar_SMTEncoding_Util.mkApp uu____9498  in
    let valid_b_x =
      let uu____9508 =
        let uu____9512 =
          let uu____9514 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9514]  in
        ("Valid", uu____9512)  in
      FStar_SMTEncoding_Util.mkApp uu____9508  in
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
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9544]  in
                      [uu____9542]  in
                    let uu____9547 =
                      let uu____9548 =
                        let uu____9551 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9551, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9548  in
                    (uu____9539, [xx1], uu____9547)  in
                  FStar_SMTEncoding_Util.mkForall uu____9533  in
                (uu____9532, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9529  in
            ([[valid]], [aa; bb], uu____9528)  in
          FStar_SMTEncoding_Util.mkForall uu____9522  in
        (uu____9521, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9517  in
    [uu____9516]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9598 =
        let uu____9602 =
          let uu____9604 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9604]  in
        ("Valid", uu____9602)  in
      FStar_SMTEncoding_Util.mkApp uu____9598  in
    let valid_b_x =
      let uu____9608 =
        let uu____9612 =
          let uu____9614 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9614]  in
        ("Valid", uu____9612)  in
      FStar_SMTEncoding_Util.mkApp uu____9608  in
    let uu____9616 =
      let uu____9617 =
        let uu____9621 =
          let uu____9622 =
            let uu____9628 =
              let uu____9629 =
                let uu____9632 =
                  let uu____9633 =
                    let uu____9639 =
                      let uu____9642 =
                        let uu____9644 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9644]  in
                      [uu____9642]  in
                    let uu____9647 =
                      let uu____9648 =
                        let uu____9651 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9651, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9648  in
                    (uu____9639, [xx1], uu____9647)  in
                  FStar_SMTEncoding_Util.mkExists uu____9633  in
                (uu____9632, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9629  in
            ([[valid]], [aa; bb], uu____9628)  in
          FStar_SMTEncoding_Util.mkForall uu____9622  in
        (uu____9621, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Term.Assume uu____9617  in
    [uu____9616]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9687 =
      let uu____9688 =
        let uu____9692 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9693 = varops.mk_unique "typing_range_const"  in
        (uu____9692, (Some "Range_const typing"), uu____9693)  in
      FStar_SMTEncoding_Term.Assume uu____9688  in
    [uu____9687]  in
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
          let uu____9955 =
            FStar_Util.find_opt
              (fun uu____9973  ->
                 match uu____9973 with
                 | (l,uu____9983) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9955 with
          | None  -> []
          | Some (uu____10005,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____10042 = encode_function_type_as_formula None None t env  in
        match uu____10042 with
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
            let uu____10074 =
              (let uu____10075 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10075) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10074
            then
              let uu____10079 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10079 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10091 =
                      let uu____10092 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10092.FStar_Syntax_Syntax.n  in
                    match uu____10091 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10097) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10114  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10117 -> []  in
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
              (let uu____10126 = prims.is lid  in
               if uu____10126
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10131 = prims.mk lid vname  in
                 match uu____10131 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10146 =
                    let uu____10152 = curried_arrow_formals_comp t_norm  in
                    match uu____10152 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10163 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10163
                          then
                            let uu____10164 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___153_10165 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___153_10165.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___153_10165.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___153_10165.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___153_10165.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___153_10165.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___153_10165.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___153_10165.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___153_10165.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___153_10165.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___153_10165.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___153_10165.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___153_10165.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___153_10165.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___153_10165.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___153_10165.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___153_10165.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___153_10165.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___153_10165.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___153_10165.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___153_10165.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___153_10165.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___153_10165.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___153_10165.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10164
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10172 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10172)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10146 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10199 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10199 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10212 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_10236  ->
                                     match uu___124_10236 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10239 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10239 with
                                          | (uu____10250,(xxsym,uu____10252))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10262 =
                                                let uu____10263 =
                                                  let uu____10267 =
                                                    let uu____10268 =
                                                      let uu____10274 =
                                                        let uu____10275 =
                                                          let uu____10278 =
                                                            let uu____10279 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10279
                                                             in
                                                          (vapp, uu____10278)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10275
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10274)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10268
                                                     in
                                                  (uu____10267,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10263
                                                 in
                                              [uu____10262])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10290 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10290 with
                                          | (uu____10301,(xxsym,uu____10303))
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
                                              let uu____10317 =
                                                let uu____10318 =
                                                  let uu____10322 =
                                                    let uu____10323 =
                                                      let uu____10329 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10329)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10323
                                                     in
                                                  (uu____10322,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10318
                                                 in
                                              [uu____10317])
                                     | uu____10338 -> []))
                              in
                           let uu____10339 = encode_binders None formals env1
                              in
                           (match uu____10339 with
                            | (vars,guards,env',decls1,uu____10355) ->
                                let uu____10362 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10367 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10367, decls1)
                                  | Some p ->
                                      let uu____10369 = encode_formula p env'
                                         in
                                      (match uu____10369 with
                                       | (g,ds) ->
                                           let uu____10376 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10376,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10362 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10385 =
                                         let uu____10389 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10389)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10385
                                        in
                                     let uu____10394 =
                                       let vname_decl =
                                         let uu____10399 =
                                           let uu____10405 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10410  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10405,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10399
                                          in
                                       let uu____10415 =
                                         let env2 =
                                           let uu___154_10419 = env1  in
                                           {
                                             bindings =
                                               (uu___154_10419.bindings);
                                             depth = (uu___154_10419.depth);
                                             tcenv = (uu___154_10419.tcenv);
                                             warn = (uu___154_10419.warn);
                                             cache = (uu___154_10419.cache);
                                             nolabels =
                                               (uu___154_10419.nolabels);
                                             use_zfuel_name =
                                               (uu___154_10419.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___154_10419.current_module_name)
                                           }  in
                                         let uu____10420 =
                                           let uu____10421 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10421  in
                                         if uu____10420
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10415 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10431::uu____10432 ->
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
                                                   let uu____10455 =
                                                     let uu____10461 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing
                                                        in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10461)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10455
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10475 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                              in
                                           let uu____10477 =
                                             match formals with
                                             | [] ->
                                                 let uu____10486 =
                                                   let uu____10487 =
                                                     let uu____10489 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10489
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10487
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10486)
                                             | uu____10492 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10497 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10497
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10499 =
                                                     let uu____10503 =
                                                       let uu____10504 =
                                                         let uu____10510 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10510)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10504
                                                        in
                                                     (uu____10503,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10499
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10477 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10394 with
                                      | (decls2,env2) ->
                                          let uu____10534 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10539 =
                                              encode_term res_t1 env'  in
                                            match uu____10539 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10547 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10547,
                                                  decls)
                                             in
                                          (match uu____10534 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10555 =
                                                   let uu____10559 =
                                                     let uu____10560 =
                                                       let uu____10566 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10566)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10560
                                                      in
                                                   (uu____10559,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10555
                                                  in
                                               let freshness =
                                                 let uu____10575 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10575
                                                 then
                                                   let uu____10578 =
                                                     let uu____10579 =
                                                       let uu____10585 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10591 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10585,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10591)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10579
                                                      in
                                                   let uu____10593 =
                                                     let uu____10595 =
                                                       pretype_axiom env2
                                                         vapp vars
                                                        in
                                                     [uu____10595]  in
                                                   uu____10578 :: uu____10593
                                                 else []  in
                                               let g =
                                                 let uu____10599 =
                                                   let uu____10601 =
                                                     let uu____10603 =
                                                       let uu____10605 =
                                                         let uu____10607 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10607
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10605
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10603
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10601
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10599
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
          let uu____10629 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10629 with
          | None  ->
              let uu____10652 = encode_free_var env x t t_norm []  in
              (match uu____10652 with
               | (decls,env1) ->
                   let uu____10667 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10667 with
                    | (n1,x',uu____10686) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10698) -> ((n1, x1), [], env)
  
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
          let uu____10731 = encode_free_var env lid t tt quals  in
          match uu____10731 with
          | (decls,env1) ->
              let uu____10742 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10742
              then
                let uu____10746 =
                  let uu____10748 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10748  in
                (uu____10746, env1)
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
             (fun uu____10776  ->
                fun lb  ->
                  match uu____10776 with
                  | (decls,env1) ->
                      let uu____10788 =
                        let uu____10792 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10792
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10788 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10806 = FStar_Syntax_Util.head_and_args t  in
    match uu____10806 with
    | (hd1,args) ->
        let uu____10832 =
          let uu____10833 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10833.FStar_Syntax_Syntax.n  in
        (match uu____10832 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10837,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10850 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10865  ->
      fun quals  ->
        match uu____10865 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10914 = FStar_Util.first_N nbinders formals  in
              match uu____10914 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10954  ->
                         fun uu____10955  ->
                           match (uu____10954, uu____10955) with
                           | ((formal,uu____10965),(binder,uu____10967)) ->
                               let uu____10972 =
                                 let uu____10977 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10977)  in
                               FStar_Syntax_Syntax.NT uu____10972) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10982 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10996  ->
                              match uu____10996 with
                              | (x,i) ->
                                  let uu____11003 =
                                    let uu___155_11004 = x  in
                                    let uu____11005 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_11004.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___155_11004.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11005
                                    }  in
                                  (uu____11003, i)))
                       in
                    FStar_All.pipe_right uu____10982
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____11017 =
                      let uu____11019 =
                        let uu____11020 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____11020.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11019
                       in
                    let uu____11024 =
                      let uu____11025 = FStar_Syntax_Subst.compress body  in
                      let uu____11026 =
                        let uu____11027 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____11027  in
                      FStar_Syntax_Syntax.extend_app_n uu____11025
                        uu____11026
                       in
                    uu____11024 uu____11017 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11069 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____11069
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___156_11070 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___156_11070.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___156_11070.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___156_11070.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___156_11070.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___156_11070.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___156_11070.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___156_11070.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___156_11070.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___156_11070.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___156_11070.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___156_11070.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___156_11070.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___156_11070.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___156_11070.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___156_11070.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___156_11070.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___156_11070.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___156_11070.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___156_11070.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___156_11070.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___156_11070.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___156_11070.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___156_11070.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____11091 = FStar_Syntax_Util.abs_formals e  in
                match uu____11091 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11140::uu____11141 ->
                         let uu____11149 =
                           let uu____11150 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11150.FStar_Syntax_Syntax.n  in
                         (match uu____11149 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11177 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11177 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11203 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11203
                                   then
                                     let uu____11221 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11221 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11267  ->
                                                   fun uu____11268  ->
                                                     match (uu____11267,
                                                             uu____11268)
                                                     with
                                                     | ((x,uu____11278),
                                                        (b,uu____11280)) ->
                                                         let uu____11285 =
                                                           let uu____11290 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11290)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11285)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11292 =
                                            let uu____11303 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11303)
                                             in
                                          (uu____11292, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11338 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11338 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11390) ->
                              let uu____11395 =
                                let uu____11406 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11406  in
                              (uu____11395, true)
                          | uu____11439 when Prims.op_Negation norm1 ->
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
                          | uu____11441 ->
                              let uu____11442 =
                                let uu____11443 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11444 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11443
                                  uu____11444
                                 in
                              failwith uu____11442)
                     | uu____11457 ->
                         let uu____11458 =
                           let uu____11459 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11459.FStar_Syntax_Syntax.n  in
                         (match uu____11458 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11486 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11486 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11504 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11504 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11552 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11580 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11580
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11587 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11628  ->
                            fun lb  ->
                              match uu____11628 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11679 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11679
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11682 =
                                      let uu____11690 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11690
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11682 with
                                    | (tok,decl,env2) ->
                                        let uu____11715 =
                                          let uu____11722 =
                                            let uu____11728 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11728, tok)  in
                                          uu____11722 :: toks  in
                                        (uu____11715, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11587 with
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
                        | uu____11830 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11835 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11835 vars)
                            else
                              (let uu____11837 =
                                 let uu____11841 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11841)  in
                               FStar_SMTEncoding_Util.mkApp uu____11837)
                         in
                      let uu____11846 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11848  ->
                                 match uu___125_11848 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11849 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11852 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11852)))
                         in
                      if uu____11846
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11872;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11874;
                                FStar_Syntax_Syntax.lbeff = uu____11875;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11916 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____11916 with
                                | (univ_subst,univ_vars1) ->
                                    let env' =
                                      let uu___159_11931 = env1  in
                                      let uu____11932 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env1.tcenv univ_vars1
                                         in
                                      {
                                        bindings = (uu___159_11931.bindings);
                                        depth = (uu___159_11931.depth);
                                        tcenv = uu____11932;
                                        warn = (uu___159_11931.warn);
                                        cache = (uu___159_11931.cache);
                                        nolabels = (uu___159_11931.nolabels);
                                        use_zfuel_name =
                                          (uu___159_11931.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___159_11931.encode_non_total_function_typ);
                                        current_module_name =
                                          (uu___159_11931.current_module_name)
                                      }  in
                                    let t_norm1 =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e1 =
                                      let uu____11935 =
                                        FStar_Syntax_Subst.subst univ_subst e
                                         in
                                      FStar_Syntax_Subst.compress uu____11935
                                       in
                                    let uu____11936 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____11936 with
                                     | ((binders,body,uu____11948,uu____11949),curry)
                                         ->
                                         ((let uu____11956 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____11956
                                           then
                                             let uu____11957 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____11958 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11957 uu____11958
                                           else ());
                                          (let uu____11960 =
                                             encode_binders None binders env'
                                              in
                                           match uu____11960 with
                                           | (vars,guards,env'1,binder_decls,uu____11976)
                                               ->
                                               let body1 =
                                                 let uu____11984 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____11984
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____11987 =
                                                 let uu____11992 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____11992
                                                 then
                                                   let uu____11998 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____11999 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____11998, uu____11999)
                                                 else
                                                   (let uu____12005 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____12005))
                                                  in
                                               (match uu____11987 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12019 =
                                                        let uu____12023 =
                                                          let uu____12024 =
                                                            let uu____12030 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____12030)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12024
                                                           in
                                                        let uu____12036 =
                                                          let uu____12038 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____12038
                                                           in
                                                        (uu____12023,
                                                          uu____12036,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Term.Assume
                                                        uu____12019
                                                       in
                                                    let uu____12040 =
                                                      let uu____12042 =
                                                        let uu____12044 =
                                                          let uu____12046 =
                                                            let uu____12048 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12048
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12046
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12044
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____12042
                                                       in
                                                    (uu____12040, env1))))))
                           | uu____12051 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12070 = varops.fresh "fuel"  in
                             (uu____12070, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____12073 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12112  ->
                                     fun uu____12113  ->
                                       match (uu____12112, uu____12113) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12195 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12195  in
                                           let gtok =
                                             let uu____12197 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12197  in
                                           let env3 =
                                             let uu____12199 =
                                               let uu____12201 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12201
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12199
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____12073 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12285
                                 t_norm uu____12287 =
                                 match (uu____12285, uu____12287) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12312;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12313;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12330 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____12330 with
                                      | (univ_subst,univ_vars1) ->
                                          let env' =
                                            let uu___160_12347 = env2  in
                                            let uu____12348 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env2.tcenv univ_vars1
                                               in
                                            {
                                              bindings =
                                                (uu___160_12347.bindings);
                                              depth = (uu___160_12347.depth);
                                              tcenv = uu____12348;
                                              warn = (uu___160_12347.warn);
                                              cache = (uu___160_12347.cache);
                                              nolabels =
                                                (uu___160_12347.nolabels);
                                              use_zfuel_name =
                                                (uu___160_12347.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___160_12347.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___160_12347.current_module_name)
                                            }  in
                                          let t_norm1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e1 =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____12352 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12352
                                            then
                                              let uu____12353 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12354 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12355 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12353 uu____12354
                                                uu____12355
                                            else ());
                                           (let uu____12357 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12357 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12379 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12379
                                                  then
                                                    let uu____12380 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12381 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12382 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12383 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12380 uu____12381
                                                      uu____12382 uu____12383
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12387 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12387 with
                                                  | (vars,guards,env'1,binder_decls,uu____12405)
                                                      ->
                                                      let decl_g =
                                                        let uu____12413 =
                                                          let uu____12419 =
                                                            let uu____12421 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12421
                                                             in
                                                          (g, uu____12419,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12413
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
                                                        let uu____12436 =
                                                          let uu____12440 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12440)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12436
                                                         in
                                                      let gsapp =
                                                        let uu____12446 =
                                                          let uu____12450 =
                                                            let uu____12452 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12452 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12450)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12446
                                                         in
                                                      let gmax =
                                                        let uu____12456 =
                                                          let uu____12460 =
                                                            let uu____12462 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12462 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12460)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12456
                                                         in
                                                      let body1 =
                                                        let uu____12466 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12466
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12468 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12468 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12479
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
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12479
                                                              in
                                                           let eqn_f =
                                                             let uu____12508
                                                               =
                                                               let uu____12512
                                                                 =
                                                                 let uu____12513
                                                                   =
                                                                   let uu____12519
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12519)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12513
                                                                  in
                                                               (uu____12512,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12508
                                                              in
                                                           let eqn_g' =
                                                             let uu____12527
                                                               =
                                                               let uu____12531
                                                                 =
                                                                 let uu____12532
                                                                   =
                                                                   let uu____12538
                                                                    =
                                                                    let uu____12539
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12549
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12547)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12543
                                                                     in
                                                                    (gsapp,
                                                                    uu____12542)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12539
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12538)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12532
                                                                  in
                                                               (uu____12531,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Term.Assume
                                                               uu____12527
                                                              in
                                                           let uu____12561 =
                                                             let uu____12566
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12566
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12583)
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
                                                                    let uu____12598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12598
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12601
                                                                    =
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12606
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12612)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12606
                                                                     in
                                                                    (uu____12605,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    uu____12601
                                                                    in
                                                                 let uu____12623
                                                                   =
                                                                   let uu____12627
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12627
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12635
                                                                    =
                                                                    let uu____12637
                                                                    =
                                                                    let uu____12638
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    let uu____12643
                                                                    =
                                                                    let uu____12649
                                                                    =
                                                                    let uu____12650
                                                                    =
                                                                    let uu____12653
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12653,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12650
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12649)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12643
                                                                     in
                                                                    (uu____12642,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12638
                                                                     in
                                                                    [uu____12637]
                                                                     in
                                                                    (d3,
                                                                    uu____12635)
                                                                    in
                                                                 (match uu____12623
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
                                                           (match uu____12561
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
                               let uu____12688 =
                                 let uu____12695 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12727  ->
                                      fun uu____12728  ->
                                        match (uu____12727, uu____12728) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12804 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12804 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12695
                                  in
                               (match uu____12688 with
                                | (decls2,eqns,env01) ->
                                    let uu____12844 =
                                      let isDeclFun uu___126_12852 =
                                        match uu___126_12852 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12853 -> true
                                        | uu____12859 -> false  in
                                      let uu____12860 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12860
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____12844 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12887 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12887
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
      (let uu____12920 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12920
       then
         let uu____12921 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12921
       else ());
      (let nm =
         let uu____12924 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12924 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12927 = encode_sigelt' env se  in
       match uu____12927 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12936 =
                  let uu____12938 =
                    let uu____12939 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12939  in
                  [uu____12938]  in
                (uu____12936, e)
            | uu____12941 ->
                let uu____12942 =
                  let uu____12944 =
                    let uu____12946 =
                      let uu____12947 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12947  in
                    uu____12946 :: g  in
                  let uu____12948 =
                    let uu____12950 =
                      let uu____12951 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12951  in
                    [uu____12950]  in
                  FStar_List.append uu____12944 uu____12948  in
                (uu____12942, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12959 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12968 =
            let uu____12969 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12969 Prims.op_Negation  in
          if uu____12968
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12989 ->
                   let uu____12990 =
                     let uu____12993 =
                       let uu____12994 =
                         let uu____13009 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13009)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____12994  in
                     FStar_Syntax_Syntax.mk uu____12993  in
                   uu____12990 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____13062 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____13062 with
               | (aname,atok,env2) ->
                   let uu____13072 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____13072 with
                    | (formals,uu____13082) ->
                        let uu____13089 =
                          let uu____13092 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____13092 env2  in
                        (match uu____13089 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13100 =
                                 let uu____13101 =
                                   let uu____13107 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13115  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13107,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____13101
                                  in
                               [uu____13100;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13122 =
                               let aux uu____13151 uu____13152 =
                                 match (uu____13151, uu____13152) with
                                 | ((bv,uu____13179),(env3,acc_sorts,acc)) ->
                                     let uu____13200 = gen_term_var env3 bv
                                        in
                                     (match uu____13200 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13122 with
                              | (uu____13238,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13252 =
                                      let uu____13256 =
                                        let uu____13257 =
                                          let uu____13263 =
                                            let uu____13264 =
                                              let uu____13267 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13267)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13264
                                             in
                                          ([[app]], xs_sorts, uu____13263)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13257
                                         in
                                      (uu____13256, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13252
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13279 =
                                      let uu____13283 =
                                        let uu____13284 =
                                          let uu____13290 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13290)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13284
                                         in
                                      (uu____13283,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____13279
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13300 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13300 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13316,uu____13317,uu____13318) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13321 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13321 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13332,t,quals) ->
          let will_encode_definition =
            let uu____13338 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_13340  ->
                      match uu___127_13340 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13343 -> false))
               in
            Prims.op_Negation uu____13338  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13349 = encode_top_level_val env fv t quals  in
             match uu____13349 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13361 =
                   let uu____13363 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13363  in
                 (uu____13361, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____13368) ->
          let uu____13371 = encode_formula f env  in
          (match uu____13371 with
           | (f1,decls) ->
               let g =
                 let uu____13380 =
                   let uu____13381 =
                     let uu____13385 =
                       let uu____13387 =
                         let uu____13388 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13388  in
                       Some uu____13387  in
                     let uu____13389 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____13385, uu____13389)  in
                   FStar_SMTEncoding_Term.Assume uu____13381  in
                 [uu____13380]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13393,quals,uu____13395) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13403 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13410 =
                       let uu____13415 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13415.FStar_Syntax_Syntax.fv_name  in
                     uu____13410.FStar_Syntax_Syntax.v  in
                   let uu____13419 =
                     let uu____13420 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13420  in
                   if uu____13419
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
                     let uu____13439 = encode_sigelt' env1 val_decl  in
                     match uu____13439 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____13403 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13456,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13458;
                          FStar_Syntax_Syntax.lbtyp = uu____13459;
                          FStar_Syntax_Syntax.lbeff = uu____13460;
                          FStar_Syntax_Syntax.lbdef = uu____13461;_}::[]),uu____13462,uu____13463,uu____13464)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13480 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13480 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13498 =
                   let uu____13502 =
                     let uu____13504 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13504]  in
                   ("Valid", uu____13502)  in
                 FStar_SMTEncoding_Util.mkApp uu____13498  in
               let decls =
                 let uu____13509 =
                   let uu____13511 =
                     let uu____13512 =
                       let uu____13516 =
                         let uu____13517 =
                           let uu____13523 =
                             let uu____13524 =
                               let uu____13527 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13527)  in
                             FStar_SMTEncoding_Util.mkEq uu____13524  in
                           ([[valid_b2t_x]], [xx], uu____13523)  in
                         FStar_SMTEncoding_Util.mkForall uu____13517  in
                       (uu____13516, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Term.Assume uu____13512  in
                   [uu____13511]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13509
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13544,uu____13545,quals,uu____13547) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13555  ->
                  match uu___128_13555 with
                  | FStar_Syntax_Syntax.Discriminator uu____13556 -> true
                  | uu____13557 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13559,lids,quals,uu____13562) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13571 =
                     let uu____13572 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13572.FStar_Ident.idText  in
                   uu____13571 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13574  ->
                     match uu___129_13574 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13575 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13578,quals,uu____13580) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13592  ->
                  match uu___130_13592 with
                  | FStar_Syntax_Syntax.Projector uu____13593 -> true
                  | uu____13596 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13603 = try_lookup_free_var env l  in
          (match uu____13603 with
           | Some uu____13607 -> ([], env)
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
          ((is_rec,bindings),uu____13616,quals,uu____13618) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13632,uu____13633) ->
          let uu____13640 = encode_signature env ses  in
          (match uu____13640 with
           | (g,env1) ->
               let uu____13650 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13660  ->
                         match uu___131_13660 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13661,Some "inversion axiom",uu____13662)
                             -> false
                         | uu____13664 -> true))
                  in
               (match uu____13650 with
                | (g',inversions) ->
                    let uu____13673 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13683  ->
                              match uu___132_13683 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13684 ->
                                  true
                              | uu____13690 -> false))
                       in
                    (match uu____13673 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13701,tps,k,uu____13704,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13715  ->
                    match uu___133_13715 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13716 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13723 = c  in
              match uu____13723 with
              | (name,args,uu____13727,uu____13728,uu____13729) ->
                  let uu____13732 =
                    let uu____13733 =
                      let uu____13739 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13746  ->
                                match uu____13746 with
                                | (uu____13750,sort,uu____13752) -> sort))
                         in
                      (name, uu____13739, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13733  in
                  [uu____13732]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13770 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13773 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13773 FStar_Option.isNone))
               in
            if uu____13770
            then []
            else
              (let uu____13790 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13790 with
               | (xxsym,xx) ->
                   let uu____13796 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13807  ->
                             fun l  ->
                               match uu____13807 with
                               | (out,decls) ->
                                   let uu____13819 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13819 with
                                    | (uu____13825,data_t) ->
                                        let uu____13827 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13827 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13856 =
                                                 let uu____13857 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13857.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13856 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13865,indices) ->
                                                   indices
                                               | uu____13881 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13893  ->
                                                         match uu____13893
                                                         with
                                                         | (x,uu____13897) ->
                                                             let uu____13898
                                                               =
                                                               let uu____13899
                                                                 =
                                                                 let uu____13903
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13903,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13899
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13898)
                                                    env)
                                                in
                                             let uu____13905 =
                                               encode_args indices env1  in
                                             (match uu____13905 with
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
                                                      let uu____13925 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13933
                                                                 =
                                                                 let uu____13936
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13936,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13933)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13925
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13938 =
                                                      let uu____13939 =
                                                        let uu____13942 =
                                                          let uu____13943 =
                                                            let uu____13946 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13946,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13943
                                                           in
                                                        (out, uu____13942)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13939
                                                       in
                                                    (uu____13938,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13796 with
                    | (data_ax,decls) ->
                        let uu____13954 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13954 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13965 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13965 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13968 =
                                 let uu____13972 =
                                   let uu____13973 =
                                     let uu____13979 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13987 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13979,
                                       uu____13987)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13973
                                    in
                                 let uu____13995 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____13972, (Some "inversion axiom"),
                                   uu____13995)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13968  in
                             let pattern_guarded_inversion =
                               let uu____13999 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____13999
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____14007 =
                                   let uu____14008 =
                                     let uu____14012 =
                                       let uu____14013 =
                                         let uu____14019 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____14027 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14019, uu____14027)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14013
                                        in
                                     let uu____14035 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____14012, (Some "inversion axiom"),
                                       uu____14035)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____14008
                                    in
                                 [uu____14007]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____14038 =
            let uu____14046 =
              let uu____14047 = FStar_Syntax_Subst.compress k  in
              uu____14047.FStar_Syntax_Syntax.n  in
            match uu____14046 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14076 -> (tps, k)  in
          (match uu____14038 with
           | (formals,res) ->
               let uu____14091 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____14091 with
                | (formals1,res1) ->
                    let uu____14098 = encode_binders None formals1 env  in
                    (match uu____14098 with
                     | (vars,guards,env',binder_decls,uu____14113) ->
                         let uu____14120 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14120 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14133 =
                                  let uu____14137 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14137)  in
                                FStar_SMTEncoding_Util.mkApp uu____14133  in
                              let uu____14142 =
                                let tname_decl =
                                  let uu____14148 =
                                    let uu____14149 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14164  ->
                                              match uu____14164 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14172 = varops.next_id ()  in
                                    (tname, uu____14149,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14172, false)
                                     in
                                  constructor_or_logic_type_decl uu____14148
                                   in
                                let uu____14177 =
                                  match vars with
                                  | [] ->
                                      let uu____14184 =
                                        let uu____14185 =
                                          let uu____14187 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14187
                                           in
                                        push_free_var env1 t tname
                                          uu____14185
                                         in
                                      ([], uu____14184)
                                  | uu____14191 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14197 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14197
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14206 =
                                          let uu____14210 =
                                            let uu____14211 =
                                              let uu____14219 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14219)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14211
                                             in
                                          (uu____14210,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____14206
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14177 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14142 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14242 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14242 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14256 =
                                               let uu____14257 =
                                                 let uu____14261 =
                                                   let uu____14262 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14262
                                                    in
                                                 (uu____14261,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14257
                                                in
                                             [uu____14256]
                                           else []  in
                                         let uu____14265 =
                                           let uu____14267 =
                                             let uu____14269 =
                                               let uu____14270 =
                                                 let uu____14274 =
                                                   let uu____14275 =
                                                     let uu____14281 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14281)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14275
                                                    in
                                                 (uu____14274, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____14270
                                                in
                                             [uu____14269]  in
                                           FStar_List.append karr uu____14267
                                            in
                                         FStar_List.append decls1 uu____14265
                                      in
                                   let aux =
                                     let uu____14290 =
                                       let uu____14292 =
                                         inversion_axioms tapp vars  in
                                       let uu____14294 =
                                         let uu____14296 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____14296]  in
                                       FStar_List.append uu____14292
                                         uu____14294
                                        in
                                     FStar_List.append kindingAx uu____14290
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14301,uu____14302,uu____14303,uu____14304,uu____14305,uu____14306)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14313,t,uu____14315,n_tps,quals,uu____14318) ->
          let uu____14323 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14323 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14334 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14334 with
                | (formals,t_res) ->
                    let uu____14356 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14356 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14365 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14365 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14403 =
                                            mk_term_projector_name d x  in
                                          (uu____14403,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14405 =
                                  let uu____14415 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14415, true)
                                   in
                                FStar_All.pipe_right uu____14405
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
                              let uu____14437 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14437 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14445::uu____14446 ->
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
                                         let uu____14471 =
                                           let uu____14477 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14477)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14471
                                     | uu____14490 -> tok_typing  in
                                   let uu____14495 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14495 with
                                    | (vars',guards',env'',decls_formals,uu____14510)
                                        ->
                                        let uu____14517 =
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
                                        (match uu____14517 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14536 ->
                                                   let uu____14540 =
                                                     let uu____14541 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14541
                                                      in
                                                   [uu____14540]
                                                in
                                             let encode_elim uu____14548 =
                                               let uu____14549 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14549 with
                                               | (head1,args) ->
                                                   let uu____14578 =
                                                     let uu____14579 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14579.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14578 with
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
                                                        let uu____14597 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14597
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
                                                                 | uu____14623
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
                                                                    let uu____14631
                                                                    =
                                                                    let uu____14632
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14632
                                                                     in
                                                                    if
                                                                    uu____14631
                                                                    then
                                                                    let uu____14639
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14639]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14641
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14654
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14654
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14676
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14680
                                                                     in
                                                                    (match uu____14676
                                                                    with
                                                                    | 
                                                                    (uu____14687,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14693
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14693
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14695
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14695
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
                                                             (match uu____14641
                                                              with
                                                              | (uu____14703,arg_vars,elim_eqns_or_guards,uu____14706)
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
                                                                    let uu____14725
                                                                    =
                                                                    let uu____14729
                                                                    =
                                                                    let uu____14730
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14743
                                                                    =
                                                                    let uu____14746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14746)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14743
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14736,
                                                                    uu____14742)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14730
                                                                     in
                                                                    (uu____14729,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14725
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14759
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14759,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14761
                                                                    =
                                                                    let uu____14765
                                                                    =
                                                                    let uu____14766
                                                                    =
                                                                    let uu____14772
                                                                    =
                                                                    let uu____14775
                                                                    =
                                                                    let uu____14777
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14777]
                                                                     in
                                                                    [uu____14775]
                                                                     in
                                                                    let uu____14780
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14785
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14784,
                                                                    uu____14785)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14781
                                                                     in
                                                                    (uu____14772,
                                                                    [x],
                                                                    uu____14780)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14766
                                                                     in
                                                                    let uu____14795
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14765,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14795)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14761
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14800
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
                                                                    (let uu____14815
                                                                    =
                                                                    let uu____14816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14816
                                                                    dapp1  in
                                                                    [uu____14815])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14800
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14820
                                                                    =
                                                                    let uu____14824
                                                                    =
                                                                    let uu____14825
                                                                    =
                                                                    let uu____14831
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14837
                                                                    =
                                                                    let uu____14838
                                                                    =
                                                                    let uu____14841
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14841)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14838
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14831,
                                                                    uu____14837)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14825
                                                                     in
                                                                    (uu____14824,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14820)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14851 ->
                                                        ((let uu____14853 =
                                                            let uu____14854 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14855 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14854
                                                              uu____14855
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14853);
                                                         ([], [])))
                                                in
                                             let uu____14858 = encode_elim ()
                                                in
                                             (match uu____14858 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14870 =
                                                      let uu____14872 =
                                                        let uu____14874 =
                                                          let uu____14876 =
                                                            let uu____14878 =
                                                              let uu____14879
                                                                =
                                                                let uu____14885
                                                                  =
                                                                  let uu____14887
                                                                    =
                                                                    let uu____14888
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14888
                                                                     in
                                                                  Some
                                                                    uu____14887
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14885)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14879
                                                               in
                                                            [uu____14878]  in
                                                          let uu____14891 =
                                                            let uu____14893 =
                                                              let uu____14895
                                                                =
                                                                let uu____14897
                                                                  =
                                                                  let uu____14899
                                                                    =
                                                                    let uu____14901
                                                                    =
                                                                    let uu____14903
                                                                    =
                                                                    let uu____14904
                                                                    =
                                                                    let uu____14908
                                                                    =
                                                                    let uu____14909
                                                                    =
                                                                    let uu____14915
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14915)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14909
                                                                     in
                                                                    (uu____14908,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14904
                                                                     in
                                                                    let uu____14922
                                                                    =
                                                                    let uu____14924
                                                                    =
                                                                    let uu____14925
                                                                    =
                                                                    let uu____14929
                                                                    =
                                                                    let uu____14930
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14942
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14936,
                                                                    uu____14942)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14930
                                                                     in
                                                                    (uu____14929,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14925
                                                                     in
                                                                    [uu____14924]
                                                                     in
                                                                    uu____14903
                                                                    ::
                                                                    uu____14922
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14901
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14899
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14897
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14895
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14893
                                                             in
                                                          FStar_List.append
                                                            uu____14876
                                                            uu____14891
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14874
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14872
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14870
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
           (fun uu____14963  ->
              fun se  ->
                match uu____14963 with
                | (g,env1) ->
                    let uu____14975 = encode_sigelt env1 se  in
                    (match uu____14975 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15011 =
        match uu____15011 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15029 ->
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
                 ((let uu____15034 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15034
                   then
                     let uu____15035 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15036 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15037 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15035 uu____15036 uu____15037
                   else ());
                  (let uu____15039 = encode_term t1 env1  in
                   match uu____15039 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15049 =
                         let uu____15053 =
                           let uu____15054 =
                             let uu____15055 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15055
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15054  in
                         new_term_constant_from_string env1 x uu____15053  in
                       (match uu____15049 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____15066 = FStar_Options.log_queries ()
                                 in
                              if uu____15066
                              then
                                let uu____15068 =
                                  let uu____15069 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15070 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15071 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15069 uu____15070 uu____15071
                                   in
                                Some uu____15068
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15082,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____15091 = encode_free_var env1 fv t t_norm []  in
                 (match uu____15091 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15110 = encode_sigelt env1 se  in
                 (match uu____15110 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15120 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15120 with | (uu____15132,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15177  ->
            match uu____15177 with
            | (l,uu____15184,uu____15185) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15206  ->
            match uu____15206 with
            | (l,uu____15214,uu____15215) ->
                let uu____15220 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____15221 =
                  let uu____15223 =
                    let uu____15224 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15224  in
                  [uu____15223]  in
                uu____15220 :: uu____15221))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15235 =
      let uu____15237 =
        let uu____15238 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15250 =
          let uu____15251 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15251 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15238;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15250
        }  in
      [uu____15237]  in
    FStar_ST.write last_env uu____15235
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15261 = FStar_ST.read last_env  in
      match uu____15261 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15267 ->
          let uu___161_15269 = e  in
          let uu____15270 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___161_15269.bindings);
            depth = (uu___161_15269.depth);
            tcenv;
            warn = (uu___161_15269.warn);
            cache = (uu___161_15269.cache);
            nolabels = (uu___161_15269.nolabels);
            use_zfuel_name = (uu___161_15269.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_15269.encode_non_total_function_typ);
            current_module_name = uu____15270
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15274 = FStar_ST.read last_env  in
    match uu____15274 with
    | [] -> failwith "Empty env stack"
    | uu____15279::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15287  ->
    let uu____15288 = FStar_ST.read last_env  in
    match uu____15288 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___162_15309 = hd1  in
          {
            bindings = (uu___162_15309.bindings);
            depth = (uu___162_15309.depth);
            tcenv = (uu___162_15309.tcenv);
            warn = (uu___162_15309.warn);
            cache = refs;
            nolabels = (uu___162_15309.nolabels);
            use_zfuel_name = (uu___162_15309.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_15309.encode_non_total_function_typ);
            current_module_name = (uu___162_15309.current_module_name)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15315  ->
    let uu____15316 = FStar_ST.read last_env  in
    match uu____15316 with
    | [] -> failwith "Popping an empty stack"
    | uu____15321::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15329  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15332  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15335  ->
    let uu____15336 = FStar_ST.read last_env  in
    match uu____15336 with
    | hd1::uu____15342::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15348 -> failwith "Impossible"
  
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
        let uu____15393 = FStar_Options.log_queries ()  in
        if uu____15393
        then
          let uu____15395 =
            let uu____15396 =
              let uu____15397 =
                let uu____15398 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15398 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15397  in
            FStar_SMTEncoding_Term.Caption uu____15396  in
          uu____15395 :: decls
        else decls  in
      let env =
        let uu____15405 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____15405 tcenv  in
      let uu____15406 = encode_sigelt env se  in
      match uu____15406 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15412 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15412))
  
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
      (let uu____15423 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15423
       then
         let uu____15424 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15424
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let uu____15429 =
         encode_signature
           (let uu___163_15433 = env  in
            {
              bindings = (uu___163_15433.bindings);
              depth = (uu___163_15433.depth);
              tcenv = (uu___163_15433.tcenv);
              warn = false;
              cache = (uu___163_15433.cache);
              nolabels = (uu___163_15433.nolabels);
              use_zfuel_name = (uu___163_15433.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_15433.encode_non_total_function_typ);
              current_module_name = (uu___163_15433.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15429 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15445 = FStar_Options.log_queries ()  in
             if uu____15445
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___164_15450 = env1  in
               {
                 bindings = (uu___164_15450.bindings);
                 depth = (uu___164_15450.depth);
                 tcenv = (uu___164_15450.tcenv);
                 warn = true;
                 cache = (uu___164_15450.cache);
                 nolabels = (uu___164_15450.nolabels);
                 use_zfuel_name = (uu___164_15450.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15450.encode_non_total_function_typ);
                 current_module_name = (uu___164_15450.current_module_name)
               });
            (let uu____15452 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15452
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
        (let uu____15487 =
           let uu____15488 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15488.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15487);
        (let env =
           let uu____15490 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____15490 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15497 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15518 = aux rest  in
                 (match uu____15518 with
                  | (out,rest1) ->
                      let t =
                        let uu____15536 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____15536 with
                        | Some uu____15540 ->
                            let uu____15541 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____15541
                              x.FStar_Syntax_Syntax.sort
                        | uu____15542 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____15545 =
                        let uu____15547 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___165_15548 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15548.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___165_15548.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____15547 :: out  in
                      (uu____15545, rest1))
             | uu____15551 -> ([], bindings1)  in
           let uu____15555 = aux bindings  in
           match uu____15555 with
           | (closing,bindings1) ->
               let uu____15569 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____15569, bindings1)
            in
         match uu____15497 with
         | (q1,bindings1) ->
             let uu____15582 =
               let uu____15585 =
                 FStar_List.filter
                   (fun uu___134_15587  ->
                      match uu___134_15587 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15588 ->
                          false
                      | uu____15592 -> true) bindings1
                  in
               encode_env_bindings env uu____15585  in
             (match uu____15582 with
              | (env_decls,env1) ->
                  ((let uu____15603 =
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
                    if uu____15603
                    then
                      let uu____15604 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15604
                    else ());
                   (let uu____15606 = encode_formula q1 env1  in
                    match uu____15606 with
                    | (phi,qdecls) ->
                        let uu____15618 =
                          let uu____15621 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15621 phi
                           in
                        (match uu____15618 with
                         | (labels,phi1) ->
                             let uu____15631 = encode_labels labels  in
                             (match uu____15631 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15652 =
                                      let uu____15656 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15657 =
                                        varops.mk_unique "@query"  in
                                      (uu____15656, (Some "query"),
                                        uu____15657)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15652
                                     in
                                  let suffix =
                                    let uu____15661 =
                                      let uu____15663 =
                                        let uu____15665 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15665
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15663
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15661
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15677 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____15677 tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15679 = encode_formula q env  in
       match uu____15679 with
       | (f,uu____15683) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15685) -> true
             | uu____15688 -> false)))
  