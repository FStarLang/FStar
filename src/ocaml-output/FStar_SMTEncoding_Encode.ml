open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
  if uu____16 then tl1 else x :: tl1 
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c) 
let vargs args =
  FStar_List.filter
    (fun uu___110_74  ->
       match uu___110_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
  
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___135_98 = a  in
        let uu____99 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____99;
          FStar_Syntax_Syntax.index = (uu___135_98.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_98.FStar_Syntax_Syntax.sort)
        }  in
      let uu____100 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____100
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____113 =
          let uu____114 =
            let uu____115 = FStar_Util.string_of_int i  in
            FStar_Util.format2
              "Projector %s on data constructor %s not found" uu____115
              lid.FStar_Ident.str
             in
          failwith uu____114  in
        let uu____116 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____116 with
        | (uu____119,t) ->
            let uu____121 =
              let uu____122 = FStar_Syntax_Subst.compress t  in
              uu____122.FStar_Syntax_Syntax.n  in
            (match uu____121 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____137 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____137 with
                  | (binders,uu____141) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____152 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____159 =
        let uu____160 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str uu____160  in
      FStar_All.pipe_left escape uu____159
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____167 =
        let uu____170 = mk_term_projector_name lid a  in
        (uu____170,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____167
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____177 =
        let uu____180 = mk_term_projector_name_by_pos lid i  in
        (uu____180,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____177
  
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
  let new_scope uu____370 =
    let uu____371 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____373 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____371, uu____373)  in
  let scopes =
    let uu____384 = let uu____390 = new_scope ()  in [uu____390]  in
    FStar_Util.mk_ref uu____384  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____415 =
        let uu____417 = FStar_ST.read scopes  in
        FStar_Util.find_map uu____417
          (fun uu____434  ->
             match uu____434 with
             | (names1,uu____441) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____415 with
      | None  -> y1
      | Some uu____446 ->
          (FStar_Util.incr ctr;
           (let uu____451 =
              let uu____452 =
                let uu____453 = FStar_ST.read ctr  in
                FStar_Util.string_of_int uu____453  in
              Prims.strcat "__" uu____452  in
            Prims.strcat y1 uu____451))
       in
    let top_scope =
      let uu____458 =
        let uu____463 = FStar_ST.read scopes  in FStar_List.hd uu____463  in
      FStar_All.pipe_left Prims.fst uu____458  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    let uu____495 =
      let uu____496 =
        let uu____497 = FStar_Util.string_of_int rn  in
        Prims.strcat "__" uu____497  in
      Prims.strcat pp.FStar_Ident.idText uu____496  in
    FStar_All.pipe_left mk_unique uu____495  in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____505 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh1 pfx =
    let uu____516 =
      let uu____517 = next_id1 ()  in
      FStar_All.pipe_left FStar_Util.string_of_int uu____517  in
    FStar_Util.format2 "%s_%s" pfx uu____516  in
  let string_const s =
    let uu____522 =
      let uu____524 = FStar_ST.read scopes  in
      FStar_Util.find_map uu____524
        (fun uu____541  ->
           match uu____541 with
           | (uu____547,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____522 with
    | Some f -> f
    | None  ->
        let id = next_id1 ()  in
        let f =
          let uu____556 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____556  in
        let top_scope =
          let uu____559 =
            let uu____564 = FStar_ST.read scopes  in FStar_List.hd uu____564
             in
          FStar_All.pipe_left Prims.snd uu____559  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____592 =
    let uu____593 =
      let uu____599 = new_scope ()  in
      let uu____604 = FStar_ST.read scopes  in uu____599 :: uu____604  in
    FStar_ST.write scopes uu____593  in
  let pop1 uu____631 =
    let uu____632 =
      let uu____638 = FStar_ST.read scopes  in FStar_List.tl uu____638  in
    FStar_ST.write scopes uu____632  in
  let mark1 uu____665 = push1 ()  in
  let reset_mark1 uu____669 = pop1 ()  in
  let commit_mark1 uu____673 =
    let uu____674 = FStar_ST.read scopes  in
    match uu____674 with
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
    | uu____734 -> failwith "Impossible"  in
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
    let uu___136_743 = x  in
    let uu____744 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____744;
      FStar_Syntax_Syntax.index = (uu___136_743.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_743.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) 
  | Binding_fvar of (FStar_Ident.lident * Prims.string *
  FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term
  Prims.option) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____765 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____789 -> false
  
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
    let uu____908 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___111_912  ->
              match uu___111_912 with
              | Binding_var (x,uu____914) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____916,uu____917,uu____918) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____908 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____951 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      if uu____951
      then
        let uu____953 = FStar_Syntax_Print.term_to_string t  in
        Some uu____953
      else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____964 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____964)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        let uu____975 = FStar_Util.string_of_int env.depth  in
        Prims.strcat "@x" uu____975  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___137_977 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_977.tcenv);
           warn = (uu___137_977.warn);
           cache = (uu___137_977.cache);
           nolabels = (uu___137_977.nolabels);
           use_zfuel_name = (uu___137_977.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_977.encode_non_total_function_typ)
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
        (let uu___138_990 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_990.depth);
           tcenv = (uu___138_990.tcenv);
           warn = (uu___138_990.warn);
           cache = (uu___138_990.cache);
           nolabels = (uu___138_990.nolabels);
           use_zfuel_name = (uu___138_990.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_990.encode_non_total_function_typ)
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
          (let uu___139_1006 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_1006.depth);
             tcenv = (uu___139_1006.tcenv);
             warn = (uu___139_1006.warn);
             cache = (uu___139_1006.cache);
             nolabels = (uu___139_1006.nolabels);
             use_zfuel_name = (uu___139_1006.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_1006.encode_non_total_function_typ)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_1016 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_1016.depth);
          tcenv = (uu___140_1016.tcenv);
          warn = (uu___140_1016.warn);
          cache = (uu___140_1016.cache);
          nolabels = (uu___140_1016.nolabels);
          use_zfuel_name = (uu___140_1016.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_1016.encode_non_total_function_typ)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___112_1032  ->
             match uu___112_1032 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1040 -> None)
         in
      let uu____1043 = aux a  in
      match uu____1043 with
      | None  ->
          let a1 = unmangle a  in
          let uu____1050 = aux a1  in
          (match uu____1050 with
           | None  ->
               let uu____1056 =
                 let uu____1057 = FStar_Syntax_Print.bv_to_string a1  in
                 FStar_Util.format1
                   "Bound term variable not found (after unmangling): %s"
                   uu____1057
                  in
               failwith uu____1056
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____1077 =
        let uu___141_1078 = env  in
        let uu____1079 =
          let uu____1081 =
            let uu____1082 =
              let uu____1089 =
                let uu____1091 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1091  in
              (x, fname, uu____1089, None)  in
            Binding_fvar uu____1082  in
          uu____1081 :: (env.bindings)  in
        {
          bindings = uu____1079;
          depth = (uu___141_1078.depth);
          tcenv = (uu___141_1078.tcenv);
          warn = (uu___141_1078.warn);
          cache = (uu___141_1078.cache);
          nolabels = (uu___141_1078.nolabels);
          use_zfuel_name = (uu___141_1078.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_1078.encode_non_total_function_typ)
        }  in
      (fname, ftok, uu____1077)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___113_1113  ->
           match uu___113_1113 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1135 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1147 =
        lookup_binding env
          (fun uu___114_1149  ->
             match uu___114_1149 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1159 -> None)
         in
      FStar_All.pipe_right uu____1147 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1172 = try_lookup_lid env a  in
      match uu____1172 with
      | None  ->
          let uu____1189 =
            let uu____1190 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____1190  in
          failwith uu____1189
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
          let uu___142_1221 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1221.depth);
            tcenv = (uu___142_1221.tcenv);
            warn = (uu___142_1221.warn);
            cache = (uu___142_1221.cache);
            nolabels = (uu___142_1221.nolabels);
            use_zfuel_name = (uu___142_1221.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1221.encode_non_total_function_typ)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1233 = lookup_lid env x  in
        match uu____1233 with
        | (t1,t2,uu____1241) ->
            let t3 =
              let uu____1247 =
                let uu____1251 =
                  let uu____1253 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____1253]  in
                (f, uu____1251)  in
              FStar_SMTEncoding_Util.mkApp uu____1247  in
            let uu___143_1256 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1256.depth);
              tcenv = (uu___143_1256.tcenv);
              warn = (uu___143_1256.warn);
              cache = (uu___143_1256.cache);
              nolabels = (uu___143_1256.nolabels);
              use_zfuel_name = (uu___143_1256.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1256.encode_non_total_function_typ)
            }
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1266 = try_lookup_lid env l  in
      match uu____1266 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1293 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1298,fuel::[]) ->
                         let uu____1301 =
                           let uu____1302 =
                             let uu____1303 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____1303 Prims.fst  in
                           FStar_Util.starts_with uu____1302 "fuel"  in
                         if uu____1301
                         then
                           let uu____1305 =
                             let uu____1306 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1306
                               fuel
                              in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1305
                         else Some t
                     | uu____1309 -> Some t)
                | uu____1310 -> None))
  
let lookup_free_var env a =
  let uu____1328 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1328 with
  | Some t -> t
  | None  ->
      let uu____1331 =
        let uu____1332 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format1 "Name not found: %s" uu____1332  in
      failwith uu____1331
  
let lookup_free_var_name env a =
  let uu____1349 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1349 with | (x,uu____1356,uu____1357) -> x 
let lookup_free_var_sym env a =
  let uu____1381 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1381 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1402;
             FStar_SMTEncoding_Term.rng = uu____1403;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1411 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1425 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___115_1434  ->
           match uu___115_1434 with
           | Binding_fvar (uu____1436,nm',tok,uu____1439) when nm = nm' ->
               tok
           | uu____1444 -> None)
  
let mkForall_fuel' n1 uu____1461 =
  match uu____1461 with
  | (pats,vars,body) ->
      let fallback uu____1477 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1480 = FStar_Options.unthrottle_inductives ()  in
      if uu____1480
      then fallback ()
      else
        (let uu____1482 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
         match uu____1482 with
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
                       | uu____1501 -> p))
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
                         let uu____1515 = add_fuel1 guards  in
                         FStar_SMTEncoding_Util.mk_and_l uu____1515
                     | uu____1517 ->
                         let uu____1518 = add_fuel1 [guard]  in
                         FStar_All.pipe_right uu____1518 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1521 -> body  in
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
          let uu____1565 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1565 FStar_Option.isNone
      | uu____1578 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1585 =
        let uu____1586 = FStar_Syntax_Util.un_uinst t  in
        uu____1586.FStar_Syntax_Syntax.n  in
      match uu____1585 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1589,uu____1590,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___116_1619  ->
                  match uu___116_1619 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1620 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1621,uu____1622,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1649 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1649 FStar_Option.isSome
      | uu____1662 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1669 = head_normal env t  in
      if uu____1669
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
    let uu____1680 =
      let uu____1684 = FStar_Syntax_Syntax.null_binder t  in [uu____1684]  in
    let uu____1685 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____1680 uu____1685 None
  
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
                    let uu____1712 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1712
                | s ->
                    let uu____1715 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1715) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___117_1727  ->
    match uu___117_1727 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1728 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1756;
                       FStar_SMTEncoding_Term.rng = uu____1757;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1771) ->
              let uu____1776 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1786 -> false) args vars)
                 in
              if uu____1776 then tok_of_name env f else None
          | (uu____1789,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t1  in
              let uu____1792 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1794 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1794))
                 in
              if uu____1792 then Some t1 else None
          | uu____1797 -> None  in
        aux t (FStar_List.rev vars)
  
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
    | uu____1881 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___118_1884  ->
    match uu___118_1884 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1886 =
          let uu____1890 =
            let uu____1892 =
              let uu____1893 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____1893  in
            [uu____1892]  in
          ("FStar.Char.Char", uu____1890)  in
        FStar_SMTEncoding_Util.mkApp uu____1886
    | FStar_Const.Const_int (i,None ) ->
        let uu____1901 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____1901
    | FStar_Const.Const_int (i,Some uu____1903) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1912) ->
        let uu____1915 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____1915
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____1919 =
          let uu____1920 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____1920  in
        failwith uu____1919
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1939 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____1947 ->
            let uu____1952 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____1952
        | uu____1953 ->
            if norm1
            then let uu____1954 = whnf env t1  in aux false uu____1954
            else
              (let uu____1956 =
                 let uu____1957 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____1958 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____1957 uu____1958
                  in
               failwith uu____1956)
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
    | uu____1979 ->
        let uu____1980 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____1980)
  
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
        (let uu____2123 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____2123
         then
           let uu____2124 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2124
         else ());
        (let uu____2126 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2162  ->
                   fun b  ->
                     match uu____2162 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2205 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2214 = gen_term_var env1 x  in
                           match uu____2214 with
                           | (xxsym,xx,env') ->
                               let uu____2228 =
                                 let uu____2231 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2231 env1 xx
                                  in
                               (match uu____2228 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2205 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2126 with
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
          let uu____2319 = encode_term t env  in
          match uu____2319 with
          | (t1,decls) ->
              let uu____2326 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2326, decls)

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
          let uu____2334 = encode_term t env  in
          match uu____2334 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2343 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2343, decls)
               | Some f ->
                   let uu____2345 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2345, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2352 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2352
       then
         let uu____2353 = FStar_Syntax_Print.tag_of_term t  in
         let uu____2354 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____2355 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2353 uu____2354
           uu____2355
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2360 =
             let uu____2361 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2362 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2363 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2364 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2361
               uu____2362 uu____2363 uu____2364
              in
           failwith uu____2360
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2368 =
             let uu____2369 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2369
              in
           failwith uu____2368
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2374) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2394) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2403 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____2403, [])
       | FStar_Syntax_Syntax.Tm_type uu____2409 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2412) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2418 = encode_const c  in (uu____2418, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2432 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2432 with
            | (binders1,res) ->
                let uu____2439 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2439
                then
                  let uu____2442 = encode_binders None binders1 env  in
                  (match uu____2442 with
                   | (vars,guards,env',decls,uu____2457) ->
                       let fsym =
                         let uu____2467 = varops.fresh "f"  in
                         (uu____2467, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2470 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2474 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2474.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2474.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2474.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2474.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2474.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2474.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2474.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2474.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2474.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2474.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2474.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2474.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2474.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2474.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2474.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2474.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2474.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2474.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2474.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2474.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2474.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2474.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2474.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____2470 with
                        | (pre_opt,res_t) ->
                            let uu____2481 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2481 with
                             | (res_pred,decls') ->
                                 let uu____2488 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2495 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____2495, [])
                                   | Some pre ->
                                       let uu____2498 =
                                         encode_formula pre env'  in
                                       (match uu____2498 with
                                        | (guard,decls0) ->
                                            let uu____2506 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____2506, decls0))
                                    in
                                 (match uu____2488 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2514 =
                                          let uu____2520 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____2520)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2514
                                         in
                                      let cvars =
                                        let uu____2530 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____2530
                                          (FStar_List.filter
                                             (fun uu____2536  ->
                                                match uu____2536 with
                                                | (x,uu____2540) ->
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
                                      let uu____2551 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2551 with
                                       | Some (t',sorts,uu____2567) ->
                                           let uu____2577 =
                                             let uu____2578 =
                                               let uu____2582 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               (t', uu____2582)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2578
                                              in
                                           (uu____2577, [])
                                       | None  ->
                                           let tsym =
                                             let uu____2598 =
                                               let uu____2599 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2599
                                                in
                                             varops.mk_unique uu____2598  in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2606 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2606
                                             then
                                               let uu____2608 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____2608
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____2614 =
                                               let uu____2618 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____2618)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2614
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
                                             let uu____2627 =
                                               let uu____2632 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____2632, a_name, a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2627
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
                                             let uu____2647 =
                                               let uu____2652 =
                                                 let uu____2653 =
                                                   let uu____2659 =
                                                     let uu____2660 =
                                                       let uu____2663 =
                                                         let uu____2664 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2664
                                                          in
                                                       (f_has_t, uu____2663)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2660
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2659)
                                                    in
                                                 mkForall_fuel uu____2653  in
                                               (uu____2652,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2647
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Some
                                                 (Prims.strcat
                                                    "interpretation_" tsym)
                                                in
                                             let uu____2679 =
                                               let uu____2684 =
                                                 let uu____2685 =
                                                   let uu____2691 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2691)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2685
                                                  in
                                               (uu____2684, a_name, a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____2679
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
                     let uu____2724 =
                       let uu____2729 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____2729, (Some "Typing for non-total arrows"),
                         a_name)
                        in
                     FStar_SMTEncoding_Term.Assume uu____2724  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Some (Prims.strcat "pre_typing_" tsym)  in
                     let uu____2740 =
                       let uu____2745 =
                         let uu____2746 =
                           let uu____2752 =
                             let uu____2753 =
                               let uu____2756 =
                                 let uu____2757 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2757
                                  in
                               (f_has_t, uu____2756)  in
                             FStar_SMTEncoding_Util.mkImp uu____2753  in
                           ([[f_has_t]], [fsym], uu____2752)  in
                         mkForall_fuel uu____2746  in
                       (uu____2745, a_name, a_name)  in
                     FStar_SMTEncoding_Term.Assume uu____2740  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2772 ->
           let uu____2777 =
             let uu____2780 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2780 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2785;
                 FStar_Syntax_Syntax.pos = uu____2786;
                 FStar_Syntax_Syntax.vars = uu____2787;_} ->
                 let uu____2794 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2794 with
                  | (b,f1) ->
                      let uu____2808 =
                        let uu____2809 = FStar_List.hd b  in
                        Prims.fst uu____2809  in
                      (uu____2808, f1))
             | uu____2814 -> failwith "impossible"  in
           (match uu____2777 with
            | (x,f) ->
                let uu____2821 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2821 with
                 | (base_t,decls) ->
                     let uu____2828 = gen_term_var env x  in
                     (match uu____2828 with
                      | (x1,xtm,env') ->
                          let uu____2837 = encode_formula f env'  in
                          (match uu____2837 with
                           | (refinement,decls') ->
                               let uu____2844 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2844 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      let uu____2852 =
                                        let uu____2855 =
                                          FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                            (Some fterm) xtm base_t
                                           in
                                        (uu____2855, refinement)  in
                                      FStar_SMTEncoding_Util.mkAnd uu____2852
                                       in
                                    let cvars =
                                      let uu____2860 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right uu____2860
                                        (FStar_List.filter
                                           (fun uu____2866  ->
                                              match uu____2866 with
                                              | (y,uu____2870) ->
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
                                    let uu____2889 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2889 with
                                     | Some (t1,uu____2904,uu____2905) ->
                                         let uu____2915 =
                                           let uu____2916 =
                                             let uu____2920 =
                                               FStar_All.pipe_right cvars
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             (t1, uu____2920)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2916
                                            in
                                         (uu____2915, [])
                                     | None  ->
                                         let tsym =
                                           let uu____2936 =
                                             let uu____2937 =
                                               FStar_Util.digest_of_string
                                                 tkey_hash
                                                in
                                             Prims.strcat "Tm_refine_"
                                               uu____2937
                                              in
                                           varops.mk_unique uu____2936  in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars  in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____2946 =
                                             let uu____2950 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars
                                                in
                                             (tsym, uu____2950)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2946
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
                                           let uu____2960 =
                                             let uu____2965 =
                                               let uu____2966 =
                                                 let uu____2972 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars,
                                                   uu____2972)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____2966
                                                in
                                             (uu____2965,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Some
                                                  (Prims.strcat "haseq" tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____2960
                                            in
                                         let t_kinding =
                                           let uu____2983 =
                                             let uu____2988 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars,
                                                   t_has_kind)
                                                in
                                             (uu____2988,
                                               (Some "refinement kinding"),
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_kinding_"
                                                     tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____2983
                                            in
                                         let t_interp =
                                           let uu____2999 =
                                             let uu____3004 =
                                               let uu____3005 =
                                                 let uu____3011 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars), uu____3011)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3005
                                                in
                                             let uu____3023 =
                                               let uu____3025 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3025  in
                                             (uu____3004, uu____3023,
                                               (Some
                                                  (Prims.strcat
                                                     "refinement_interpretation_"
                                                     tsym)))
                                              in
                                           FStar_SMTEncoding_Term.Assume
                                             uu____2999
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
             let uu____3054 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3054  in
           let uu____3058 = encode_term_pred None k env ttm  in
           (match uu____3058 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3066 =
                    let uu____3071 =
                      let uu____3073 =
                        let uu____3074 =
                          let uu____3075 =
                            let uu____3076 = FStar_Unionfind.uvar_id uv  in
                            FStar_All.pipe_left FStar_Util.string_of_int
                              uu____3076
                             in
                          FStar_Util.format1 "uvar_typing_%s" uu____3075  in
                        varops.mk_unique uu____3074  in
                      Some uu____3073  in
                    (t_has_k, (Some "Uvar typing"), uu____3071)  in
                  FStar_SMTEncoding_Term.Assume uu____3066  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3083 ->
           let uu____3093 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3093 with
            | (head1,args_e) ->
                let uu____3121 =
                  let uu____3129 =
                    let uu____3130 = FStar_Syntax_Subst.compress head1  in
                    uu____3130.FStar_Syntax_Syntax.n  in
                  (uu____3129, args_e)  in
                (match uu____3121 with
                 | (uu____3140,uu____3141) when head_redex env head1 ->
                     let uu____3152 = whnf env t  in
                     encode_term uu____3152 env
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
                     let uu____3226 = encode_term v1 env  in
                     (match uu____3226 with
                      | (v11,decls1) ->
                          let uu____3233 = encode_term v2 env  in
                          (match uu____3233 with
                           | (v21,decls2) ->
                               let uu____3240 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3240,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3242::uu____3243::uu____3244) ->
                     let e0 =
                       let uu____3274 =
                         let uu____3277 =
                           let uu____3278 =
                             let uu____3288 =
                               let uu____3294 = FStar_List.hd args_e  in
                               [uu____3294]  in
                             (head1, uu____3288)  in
                           FStar_Syntax_Syntax.Tm_app uu____3278  in
                         FStar_Syntax_Syntax.mk uu____3277  in
                       uu____3274 None head1.FStar_Syntax_Syntax.pos  in
                     let e =
                       let uu____3329 =
                         let uu____3332 =
                           let uu____3333 =
                             let uu____3343 = FStar_List.tl args_e  in
                             (e0, uu____3343)  in
                           FStar_Syntax_Syntax.Tm_app uu____3333  in
                         FStar_Syntax_Syntax.mk uu____3332  in
                       uu____3329 None t0.FStar_Syntax_Syntax.pos  in
                     encode_term e env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),(arg,uu____3369)::[]) ->
                     let uu____3387 = encode_term arg env  in
                     (match uu____3387 with
                      | (tm,decls) ->
                          let uu____3394 =
                            FStar_SMTEncoding_Util.mkApp ("Reify", [tm])  in
                          (uu____3394, decls))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3396),(arg,uu____3398)::[]) -> encode_term arg env
                 | uu____3416 ->
                     let uu____3424 = encode_args args_e env  in
                     (match uu____3424 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3453 = encode_term head1 env  in
                            match uu____3453 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3484 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3484 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3526  ->
                                                 fun uu____3527  ->
                                                   match (uu____3526,
                                                           uu____3527)
                                                   with
                                                   | ((bv,uu____3541),
                                                      (a,uu____3543)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3557 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3557
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3558 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3558 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3568 =
                                                   let uu____3573 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3578 =
                                                     let uu____3580 =
                                                       let uu____3581 =
                                                         let uu____3582 =
                                                           let uu____3583 =
                                                             FStar_SMTEncoding_Term.hash_of_term
                                                               app_tm
                                                              in
                                                           FStar_Util.digest_of_string
                                                             uu____3583
                                                            in
                                                         Prims.strcat
                                                           "partial_app_typing_"
                                                           uu____3582
                                                          in
                                                       varops.mk_unique
                                                         uu____3581
                                                        in
                                                     Some uu____3580  in
                                                   (uu____3573,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3578)
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____3568
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3601 = lookup_free_var_sym env fv  in
                            match uu____3601 with
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
                                let uu____3639 =
                                  let uu____3640 =
                                    FStar_TypeChecker_Env.lookup_lid
                                      env.tcenv
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     in
                                  FStar_All.pipe_right uu____3640 Prims.snd
                                   in
                                Some uu____3639
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3649,FStar_Util.Inl t1,uu____3651) ->
                                Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3672,FStar_Util.Inr c,uu____3674) ->
                                let uu____3693 =
                                  FStar_TypeChecker_Env.result_typ env.tcenv
                                    c
                                   in
                                Some uu____3693
                            | uu____3694 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3712 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3712
                                  in
                               let uu____3713 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____3713 with
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
                                     | uu____3738 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3781 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3781 with
            | (bs1,body1,opening) ->
                let fallback uu____3796 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____3801 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____3801, [decl])  in
                let is_impure uu___119_3811 =
                  match uu___119_3811 with
                  | FStar_Util.Inl lc ->
                      let uu____3821 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc  in
                      Prims.op_Negation uu____3821
                  | FStar_Util.Inr (eff,uu____3823) ->
                      let uu____3829 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____3829 Prims.op_Negation
                   in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3850 =
                        let uu____3851 =
                          lc1.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____3851  in
                      FStar_All.pipe_right uu____3850
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3863 =
                        let uu____3864 =
                          FStar_TypeChecker_Env.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____3864 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3872 =
                          let uu____3873 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____3873  in
                        FStar_All.pipe_right uu____3872
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3877 =
                             let uu____3878 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____3878  in
                           FStar_All.pipe_right uu____3877
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____3889 =
                         let uu____3890 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s"
                           uu____3890
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3889);
                      fallback ())
                 | Some lc ->
                     let uu____3902 = is_impure lc  in
                     if uu____3902
                     then fallback ()
                     else
                       (let uu____3906 = encode_binders None bs1 env  in
                        match uu____3906 with
                        | (vars,guards,envbody,decls,uu____3921) ->
                            let uu____3928 = encode_term body1 envbody  in
                            (match uu____3928 with
                             | (body2,decls') ->
                                 let key_body =
                                   let uu____3936 =
                                     let uu____3942 =
                                       let uu____3943 =
                                         let uu____3946 =
                                           FStar_SMTEncoding_Util.mk_and_l
                                             guards
                                            in
                                         (uu____3946, body2)  in
                                       FStar_SMTEncoding_Util.mkImp
                                         uu____3943
                                        in
                                     ([], vars, uu____3942)  in
                                   FStar_SMTEncoding_Util.mkForall uu____3936
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
                                   FStar_SMTEncoding_Term.hash_of_term tkey
                                    in
                                 let uu____3957 =
                                   FStar_Util.smap_try_find env.cache
                                     tkey_hash
                                    in
                                 (match uu____3957 with
                                  | Some (t1,uu____3972,uu____3973) ->
                                      let uu____3983 =
                                        let uu____3984 =
                                          let uu____3988 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              cvars
                                             in
                                          (t1, uu____3988)  in
                                        FStar_SMTEncoding_Util.mkApp
                                          uu____3984
                                         in
                                      (uu____3983, [])
                                  | None  ->
                                      let uu____3999 = is_eta env vars body2
                                         in
                                      (match uu____3999 with
                                       | Some t1 -> (t1, [])
                                       | None  ->
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let fsym =
                                             let uu____4010 =
                                               let uu____4011 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_abs_"
                                                 uu____4011
                                                in
                                             varops.mk_unique uu____4010  in
                                           let fdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (fsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 None)
                                              in
                                           let f =
                                             let uu____4016 =
                                               let uu____4020 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (fsym, uu____4020)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4016
                                              in
                                           let app = mk_Apply f vars  in
                                           let typing_f =
                                             let uu____4028 = codomain_eff lc
                                                in
                                             match uu____4028 with
                                             | None  -> []
                                             | Some c ->
                                                 let tfun =
                                                   FStar_Syntax_Util.arrow
                                                     bs1 c
                                                    in
                                                 let uu____4033 =
                                                   encode_term_pred None tfun
                                                     env f
                                                    in
                                                 (match uu____4033 with
                                                  | (f_has_t,decls'') ->
                                                      let a_name =
                                                        Some
                                                          (Prims.strcat
                                                             "typing_" fsym)
                                                         in
                                                      let uu____4041 =
                                                        let uu____4043 =
                                                          let uu____4044 =
                                                            let uu____4049 =
                                                              FStar_SMTEncoding_Util.mkForall
                                                                ([[f]],
                                                                  cvars,
                                                                  f_has_t)
                                                               in
                                                            (uu____4049,
                                                              a_name, a_name)
                                                             in
                                                          FStar_SMTEncoding_Term.Assume
                                                            uu____4044
                                                           in
                                                        [uu____4043]  in
                                                      FStar_List.append
                                                        decls'' uu____4041)
                                              in
                                           let interp_f =
                                             let a_name =
                                               Some
                                                 (Prims.strcat
                                                    "interpretation_" fsym)
                                                in
                                             let uu____4059 =
                                               let uu____4064 =
                                                 let uu____4065 =
                                                   let uu____4071 =
                                                     FStar_SMTEncoding_Util.mkEq
                                                       (app, body2)
                                                      in
                                                   ([[app]],
                                                     (FStar_List.append vars
                                                        cvars), uu____4071)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4065
                                                  in
                                               (uu____4064, a_name, a_name)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               uu____4059
                                              in
                                           let f_decls =
                                             FStar_List.append decls
                                               (FStar_List.append decls'
                                                  (FStar_List.append (fdecl
                                                     :: typing_f) [interp_f]))
                                              in
                                           (FStar_Util.smap_add env.cache
                                              tkey_hash
                                              (fsym, cvar_sorts, f_decls);
                                            (f, f_decls))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4090,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4091;
                          FStar_Syntax_Syntax.lbunivs = uu____4092;
                          FStar_Syntax_Syntax.lbtyp = uu____4093;
                          FStar_Syntax_Syntax.lbeff = uu____4094;
                          FStar_Syntax_Syntax.lbdef = uu____4095;_}::uu____4096),uu____4097)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4115;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4117;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4133 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4146 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4146, [decl_e])))
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
              let uu____4188 = encode_term e1 env  in
              match uu____4188 with
              | (ee1,decls1) ->
                  let uu____4195 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4195 with
                   | (xs,e21) ->
                       let uu____4209 = FStar_List.hd xs  in
                       (match uu____4209 with
                        | (x1,uu____4217) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4219 = encode_body e21 env'  in
                            (match uu____4219 with
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
            let uu____4241 = encode_term e env  in
            match uu____4241 with
            | (scr,decls) ->
                let uu____4248 =
                  FStar_List.fold_right
                    (fun b  ->
                       fun uu____4256  ->
                         match uu____4256 with
                         | (else_case,decls1) ->
                             let uu____4267 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4267 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p  in
                                  FStar_List.fold_right
                                    (fun uu____4297  ->
                                       fun uu____4298  ->
                                         match (uu____4297, uu____4298) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr
                                                in
                                             let projections =
                                               pattern.projections scr  in
                                             let env1 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____4335  ->
                                                         match uu____4335
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env1 x t) env)
                                                in
                                             let uu____4340 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4355 =
                                                     encode_term w1 env1  in
                                                   (match uu____4355 with
                                                    | (w2,decls21) ->
                                                        let uu____4363 =
                                                          let uu____4364 =
                                                            let uu____4367 =
                                                              let uu____4368
                                                                =
                                                                let uu____4371
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                   in
                                                                (w2,
                                                                  uu____4371)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4368
                                                               in
                                                            (guard,
                                                              uu____4367)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4364
                                                           in
                                                        (uu____4363, decls21))
                                                in
                                             (match uu____4340 with
                                              | (guard1,decls21) ->
                                                  let uu____4379 =
                                                    encode_br br env1  in
                                                  (match uu____4379 with
                                                   | (br1,decls3) ->
                                                       let uu____4387 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1)
                                                          in
                                                       (uu____4387,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1))) pats
                    (default_case, decls)
                   in
                (match uu____4248 with
                 | (match_tm,decls1) -> (match_tm, decls1))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4411 ->
          let uu____4412 = encode_one_pat env pat  in [uu____4412]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4424 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4424
       then
         let uu____4425 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4425
       else ());
      (let uu____4427 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4427 with
       | (vars,pat_term) ->
           let uu____4437 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4460  ->
                     fun v1  ->
                       match uu____4460 with
                       | (env1,vars1) ->
                           let uu____4488 = gen_term_var env1 v1  in
                           (match uu____4488 with
                            | (xx,uu____4500,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____4437 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4547 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4555 =
                        let uu____4558 = encode_const c  in
                        (scrutinee, uu____4558)  in
                      FStar_SMTEncoding_Util.mkEq uu____4555
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        mk_data_tester env1
                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4589  ->
                                  match uu____4589 with
                                  | (arg,uu____4595) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4605 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____4605))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4624 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4639 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4654 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4676  ->
                                  match uu____4676 with
                                  | (arg,uu____4685) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____4695 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____4695))
                         in
                      FStar_All.pipe_right uu____4654 FStar_List.flatten
                   in
                let pat_term1 uu____4711 = encode_term pat_term env1  in
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
      let uu____4718 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4733  ->
                fun uu____4734  ->
                  match (uu____4733, uu____4734) with
                  | ((tms,decls),(t,uu____4754)) ->
                      let uu____4765 = encode_term t env  in
                      (match uu____4765 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____4718 with | (l1,decls) -> ((FStar_List.rev l1), decls)

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
            let uu____4803 = FStar_Syntax_Util.list_elements e  in
            match uu____4803 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____4821 =
              let uu____4831 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right uu____4831 FStar_Syntax_Util.head_and_args
               in
            match uu____4821 with
            | (head1,args) ->
                let uu____4862 =
                  let uu____4870 =
                    let uu____4871 = FStar_Syntax_Util.un_uinst head1  in
                    uu____4871.FStar_Syntax_Syntax.n  in
                  (uu____4870, args)  in
                (match uu____4862 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____4885,uu____4886)::(e,uu____4888)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4919)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____4940 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements1 p  in
            let smt_pat_or t1 =
              let uu____4973 =
                let uu____4983 = FStar_Syntax_Util.unmeta t1  in
                FStar_All.pipe_right uu____4983
                  FStar_Syntax_Util.head_and_args
                 in
              match uu____4973 with
              | (head1,args) ->
                  let uu____5012 =
                    let uu____5020 =
                      let uu____5021 = FStar_Syntax_Util.un_uinst head1  in
                      uu____5021.FStar_Syntax_Syntax.n  in
                    (uu____5020, args)  in
                  (match uu____5012 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5034)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5054 -> None)
               in
            match elts with
            | t1::[] ->
                let uu____5072 = smt_pat_or t1  in
                (match uu____5072 with
                 | Some e ->
                     let uu____5088 = list_elements1 e  in
                     FStar_All.pipe_right uu____5088
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5105 = list_elements1 branch1  in
                             FStar_All.pipe_right uu____5105
                               (FStar_List.map one_pat)))
                 | uu____5119 ->
                     let uu____5123 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [uu____5123])
            | uu____5154 ->
                let uu____5156 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [uu____5156]
             in
          let uu____5187 =
            let uu____5203 =
              let uu____5204 = FStar_Syntax_Subst.compress t  in
              uu____5204.FStar_Syntax_Syntax.n  in
            match uu____5203 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5234 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____5234 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_typ_name = uu____5269;
                            FStar_Syntax_Syntax.comp_univs = uu____5270;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5272)::(post,uu____5274)::(pats,uu____5276)::[];
                            FStar_Syntax_Syntax.flags = uu____5277;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let uu____5309 = lemma_pats pats'  in
                          (binders1, pre, post, uu____5309)
                      | uu____5328 -> failwith "impos"))
            | uu____5344 -> failwith "Impos"  in
          match uu____5187 with
          | (binders,pre,post,patterns) ->
              let uu____5388 = encode_binders None binders env  in
              (match uu____5388 with
               | (vars,guards,env1,decls,uu____5403) ->
                   let uu____5410 =
                     let uu____5417 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5448 =
                                 let uu____5453 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5469  ->
                                           match uu____5469 with
                                           | (t1,uu____5476) ->
                                               encode_term t1
                                                 (let uu___145_5479 = env1
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___145_5479.bindings);
                                                    depth =
                                                      (uu___145_5479.depth);
                                                    tcenv =
                                                      (uu___145_5479.tcenv);
                                                    warn =
                                                      (uu___145_5479.warn);
                                                    cache =
                                                      (uu___145_5479.cache);
                                                    nolabels =
                                                      (uu___145_5479.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___145_5479.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right uu____5453
                                   FStar_List.unzip
                                  in
                               match uu____5448 with
                               | (pats,decls1) -> (pats, decls1)))
                        in
                     FStar_All.pipe_right uu____5417 FStar_List.unzip  in
                   (match uu____5410 with
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
                                           let uu____5543 =
                                             let uu____5544 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5544 e
                                              in
                                           uu____5543 :: p))
                               | uu____5545 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5574 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e
                                                    in
                                                 uu____5574 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5582 =
                                           let uu____5583 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5583 tl1
                                            in
                                         aux uu____5582 vars2
                                     | uu____5584 -> pats  in
                                   let uu____5588 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux uu____5588 vars)
                           in
                        let env2 =
                          let uu___146_5590 = env1  in
                          {
                            bindings = (uu___146_5590.bindings);
                            depth = (uu___146_5590.depth);
                            tcenv = (uu___146_5590.tcenv);
                            warn = (uu___146_5590.warn);
                            cache = (uu___146_5590.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___146_5590.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___146_5590.encode_non_total_function_typ)
                          }  in
                        let uu____5591 =
                          let uu____5594 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula uu____5594 env2  in
                        (match uu____5591 with
                         | (pre1,decls'') ->
                             let uu____5599 =
                               let uu____5602 = FStar_Syntax_Util.unmeta post
                                  in
                               encode_formula uu____5602 env2  in
                             (match uu____5599 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let uu____5609 =
                                    let uu____5610 =
                                      let uu____5616 =
                                        let uu____5617 =
                                          let uu____5620 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards)
                                             in
                                          (uu____5620, post1)  in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5617
                                         in
                                      (pats1, vars, uu____5616)  in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5610
                                     in
                                  (uu____5609, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5633 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5633
        then
          let uu____5634 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____5635 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5634 uu____5635
        else ()  in
      let enc f r l =
        let uu____5662 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5675 = encode_term (Prims.fst x) env  in
                 match uu____5675 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5662 with
        | (decls,args) ->
            let uu____5692 =
              let uu___147_5693 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___147_5693.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___147_5693.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____5692, decls)
         in
      let const_op f r uu____5712 = let uu____5715 = f r  in (uu____5715, [])
         in
      let un_op f l =
        let uu____5731 = FStar_List.hd l  in FStar_All.pipe_left f uu____5731
         in
      let bin_op f uu___120_5744 =
        match uu___120_5744 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5752 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____5779 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5788  ->
                 match uu____5788 with
                 | (t,uu____5796) ->
                     let uu____5797 = encode_formula t env  in
                     (match uu____5797 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____5779 with
        | (decls,phis) ->
            let uu____5814 =
              let uu___148_5815 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_5815.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_5815.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____5814, decls)
         in
      let eq_op r uu___121_5831 =
        match uu___121_5831 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____5891 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____5891 r [e1; e2]
        | l ->
            let uu____5911 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____5911 r l
         in
      let mk_imp1 r uu___122_5930 =
        match uu___122_5930 with
        | (lhs,uu____5934)::(rhs,uu____5936)::[] ->
            let uu____5957 = encode_formula rhs env  in
            (match uu____5957 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____5966) ->
                      (l1, decls1)
                  | uu____5969 ->
                      let uu____5970 = encode_formula lhs env  in
                      (match uu____5970 with
                       | (l2,decls2) ->
                           let uu____5977 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____5977, (FStar_List.append decls1 decls2)))))
        | uu____5979 -> failwith "impossible"  in
      let mk_ite r uu___123_5994 =
        match uu___123_5994 with
        | (guard,uu____5998)::(_then,uu____6000)::(_else,uu____6002)::[] ->
            let uu____6031 = encode_formula guard env  in
            (match uu____6031 with
             | (g,decls1) ->
                 let uu____6038 = encode_formula _then env  in
                 (match uu____6038 with
                  | (t,decls2) ->
                      let uu____6045 = encode_formula _else env  in
                      (match uu____6045 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6054 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6073 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6073  in
      let connectives =
        let uu____6085 =
          let uu____6094 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6094)  in
        let uu____6107 =
          let uu____6117 =
            let uu____6126 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6126)  in
          let uu____6139 =
            let uu____6149 =
              let uu____6159 =
                let uu____6168 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6168)  in
              let uu____6181 =
                let uu____6191 =
                  let uu____6201 =
                    let uu____6210 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6210)  in
                  [uu____6201;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6191  in
              uu____6159 :: uu____6181  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6149  in
          uu____6117 :: uu____6139  in
        uu____6085 :: uu____6107  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6372 = encode_formula phi' env  in
            (match uu____6372 with
             | (phi2,decls) ->
                 let uu____6379 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6379, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6380 ->
            let uu____6385 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6385 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6414 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6414 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6422;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6424;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6440 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____6440 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6472::(x,uu____6474)::(t,uu____6476)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6510 = encode_term x env  in
                 (match uu____6510 with
                  | (x1,decls) ->
                      let uu____6517 = encode_term t env  in
                      (match uu____6517 with
                       | (t1,decls') ->
                           let uu____6524 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____6524, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6528)::(msg,uu____6530)::(phi2,uu____6532)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6566 =
                   let uu____6569 =
                     let uu____6570 = FStar_Syntax_Subst.compress r  in
                     uu____6570.FStar_Syntax_Syntax.n  in
                   let uu____6573 =
                     let uu____6574 = FStar_Syntax_Subst.compress msg  in
                     uu____6574.FStar_Syntax_Syntax.n  in
                   (uu____6569, uu____6573)  in
                 (match uu____6566 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6581))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____6597 -> fallback phi2)
             | uu____6600 when head_redex env head2 ->
                 let uu____6608 = whnf env phi1  in
                 encode_formula uu____6608 env
             | uu____6609 ->
                 let uu____6617 = encode_term phi1 env  in
                 (match uu____6617 with
                  | (tt,decls) ->
                      let uu____6624 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___149_6625 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___149_6625.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___149_6625.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____6624, decls)))
        | uu____6628 ->
            let uu____6629 = encode_term phi1 env  in
            (match uu____6629 with
             | (tt,decls) ->
                 let uu____6636 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___150_6637 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___150_6637.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___150_6637.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____6636, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____6664 = encode_binders None bs env1  in
        match uu____6664 with
        | (vars,guards,env2,decls,uu____6686) ->
            let uu____6693 =
              let uu____6700 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6723 =
                          let uu____6728 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6742  ->
                                    match uu____6742 with
                                    | (t,uu____6748) ->
                                        encode_term t
                                          (let uu___151_6749 = env2  in
                                           {
                                             bindings =
                                               (uu___151_6749.bindings);
                                             depth = (uu___151_6749.depth);
                                             tcenv = (uu___151_6749.tcenv);
                                             warn = (uu___151_6749.warn);
                                             cache = (uu___151_6749.cache);
                                             nolabels =
                                               (uu___151_6749.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___151_6749.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right uu____6728 FStar_List.unzip
                           in
                        match uu____6723 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____6700 FStar_List.unzip  in
            (match uu____6693 with
             | (pats,decls') ->
                 let uu____6801 = encode_formula body env2  in
                 (match uu____6801 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6820;
                             FStar_SMTEncoding_Term.rng = uu____6821;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6829 -> guards  in
                      let uu____6832 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____6832, body1,
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
                (fun uu____6866  ->
                   match uu____6866 with
                   | (x,uu____6870) ->
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
               let uu____6876 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____6882 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____6882) uu____6876 tl1
                in
             let uu____6884 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6896  ->
                       match uu____6896 with
                       | (b,uu____6900) ->
                           let uu____6901 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____6901))
                in
             (match uu____6884 with
              | None  -> ()
              | Some (x,uu____6905) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____6915 =
                    let uu____6916 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____6916
                     in
                  FStar_Errors.warn pos uu____6915)
          in
       let uu____6917 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____6917 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6923 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____6959  ->
                     match uu____6959 with
                     | (l,uu____6969) -> FStar_Ident.lid_equals op l))
              in
           (match uu____6923 with
            | None  -> fallback phi1
            | Some (uu____6992,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7021 = encode_q_body env vars pats body  in
             match uu____7021 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7047 =
                     let uu____7053 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7053)  in
                   FStar_SMTEncoding_Term.mkForall uu____7047
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7065 = encode_q_body env vars pats body  in
             match uu____7065 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7090 =
                   let uu____7091 =
                     let uu____7097 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7097)  in
                   FStar_SMTEncoding_Term.mkExists uu____7091
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7090, decls))))

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
  let uu____7146 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7146 with
  | (asym,a) ->
      let uu____7151 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7151 with
       | (xsym,x) ->
           let uu____7156 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7156 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7186 =
                      let uu____7192 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                         in
                      (x1, uu____7192, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7186  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7207 =
                      let uu____7211 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7211)  in
                    FStar_SMTEncoding_Util.mkApp uu____7207  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7219 =
                    let uu____7221 =
                      let uu____7223 =
                        let uu____7225 =
                          let uu____7226 =
                            let uu____7231 =
                              let uu____7232 =
                                let uu____7238 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7238)  in
                              FStar_SMTEncoding_Util.mkForall uu____7232  in
                            (uu____7231, None,
                              (Some (Prims.strcat "primitive_" x1)))
                             in
                          FStar_SMTEncoding_Term.Assume uu____7226  in
                        let uu____7248 =
                          let uu____7250 =
                            let uu____7251 =
                              let uu____7256 =
                                let uu____7257 =
                                  let uu____7263 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7263)  in
                                FStar_SMTEncoding_Util.mkForall uu____7257
                                 in
                              (uu____7256,
                                (Some "Name-token correspondence"),
                                (Some
                                   (Prims.strcat "token_correspondence_" x1)))
                               in
                            FStar_SMTEncoding_Term.Assume uu____7251  in
                          [uu____7250]  in
                        uu____7225 :: uu____7248  in
                      xtok_decl :: uu____7223  in
                    xname_decl :: uu____7221  in
                  (xtok1, uu____7219)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7313 =
                    let uu____7321 =
                      let uu____7327 =
                        let uu____7328 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7328
                         in
                      quant axy uu____7327  in
                    (FStar_Syntax_Const.op_Eq, uu____7321)  in
                  let uu____7334 =
                    let uu____7343 =
                      let uu____7351 =
                        let uu____7357 =
                          let uu____7358 =
                            let uu____7359 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7359  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7358
                           in
                        quant axy uu____7357  in
                      (FStar_Syntax_Const.op_notEq, uu____7351)  in
                    let uu____7365 =
                      let uu____7374 =
                        let uu____7382 =
                          let uu____7388 =
                            let uu____7389 =
                              let uu____7390 =
                                let uu____7393 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7394 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7393, uu____7394)  in
                              FStar_SMTEncoding_Util.mkLT uu____7390  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7389
                             in
                          quant xy uu____7388  in
                        (FStar_Syntax_Const.op_LT, uu____7382)  in
                      let uu____7400 =
                        let uu____7409 =
                          let uu____7417 =
                            let uu____7423 =
                              let uu____7424 =
                                let uu____7425 =
                                  let uu____7428 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____7429 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7428, uu____7429)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7425  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7424
                               in
                            quant xy uu____7423  in
                          (FStar_Syntax_Const.op_LTE, uu____7417)  in
                        let uu____7435 =
                          let uu____7444 =
                            let uu____7452 =
                              let uu____7458 =
                                let uu____7459 =
                                  let uu____7460 =
                                    let uu____7463 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____7464 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____7463, uu____7464)  in
                                  FStar_SMTEncoding_Util.mkGT uu____7460  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7459
                                 in
                              quant xy uu____7458  in
                            (FStar_Syntax_Const.op_GT, uu____7452)  in
                          let uu____7470 =
                            let uu____7479 =
                              let uu____7487 =
                                let uu____7493 =
                                  let uu____7494 =
                                    let uu____7495 =
                                      let uu____7498 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____7499 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____7498, uu____7499)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____7495
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7494
                                   in
                                quant xy uu____7493  in
                              (FStar_Syntax_Const.op_GTE, uu____7487)  in
                            let uu____7505 =
                              let uu____7514 =
                                let uu____7522 =
                                  let uu____7528 =
                                    let uu____7529 =
                                      let uu____7530 =
                                        let uu____7533 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____7534 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____7533, uu____7534)  in
                                      FStar_SMTEncoding_Util.mkSub uu____7530
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7529
                                     in
                                  quant xy uu____7528  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7522)
                                 in
                              let uu____7540 =
                                let uu____7549 =
                                  let uu____7557 =
                                    let uu____7563 =
                                      let uu____7564 =
                                        let uu____7565 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7565
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7564
                                       in
                                    quant qx uu____7563  in
                                  (FStar_Syntax_Const.op_Minus, uu____7557)
                                   in
                                let uu____7571 =
                                  let uu____7580 =
                                    let uu____7588 =
                                      let uu____7594 =
                                        let uu____7595 =
                                          let uu____7596 =
                                            let uu____7599 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____7600 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____7599, uu____7600)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7596
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7595
                                         in
                                      quant xy uu____7594  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7588)
                                     in
                                  let uu____7606 =
                                    let uu____7615 =
                                      let uu____7623 =
                                        let uu____7629 =
                                          let uu____7630 =
                                            let uu____7631 =
                                              let uu____7634 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____7635 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____7634, uu____7635)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7631
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7630
                                           in
                                        quant xy uu____7629  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7623)
                                       in
                                    let uu____7641 =
                                      let uu____7650 =
                                        let uu____7658 =
                                          let uu____7664 =
                                            let uu____7665 =
                                              let uu____7666 =
                                                let uu____7669 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____7670 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____7669, uu____7670)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7666
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7665
                                             in
                                          quant xy uu____7664  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7658)
                                         in
                                      let uu____7676 =
                                        let uu____7685 =
                                          let uu____7693 =
                                            let uu____7699 =
                                              let uu____7700 =
                                                let uu____7701 =
                                                  let uu____7704 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____7705 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____7704, uu____7705)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7701
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7700
                                               in
                                            quant xy uu____7699  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7693)
                                           in
                                        let uu____7711 =
                                          let uu____7720 =
                                            let uu____7728 =
                                              let uu____7734 =
                                                let uu____7735 =
                                                  let uu____7736 =
                                                    let uu____7739 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____7740 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____7739, uu____7740)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7736
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7735
                                                 in
                                              quant xy uu____7734  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7728)
                                             in
                                          let uu____7746 =
                                            let uu____7755 =
                                              let uu____7763 =
                                                let uu____7769 =
                                                  let uu____7770 =
                                                    let uu____7771 =
                                                      let uu____7774 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____7775 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____7774,
                                                        uu____7775)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7771
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7770
                                                   in
                                                quant xy uu____7769  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7763)
                                               in
                                            let uu____7781 =
                                              let uu____7790 =
                                                let uu____7798 =
                                                  let uu____7804 =
                                                    let uu____7805 =
                                                      let uu____7806 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7806
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7805
                                                     in
                                                  quant qx uu____7804  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7798)
                                                 in
                                              [uu____7790]  in
                                            uu____7755 :: uu____7781  in
                                          uu____7720 :: uu____7746  in
                                        uu____7685 :: uu____7711  in
                                      uu____7650 :: uu____7676  in
                                    uu____7615 :: uu____7641  in
                                  uu____7580 :: uu____7606  in
                                uu____7549 :: uu____7571  in
                              uu____7514 :: uu____7540  in
                            uu____7479 :: uu____7505  in
                          uu____7444 :: uu____7470  in
                        uu____7409 :: uu____7435  in
                      uu____7374 :: uu____7400  in
                    uu____7343 :: uu____7365  in
                  uu____7313 :: uu____7334  in
                let mk1 l v1 =
                  let uu____7934 =
                    let uu____7939 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____7971  ->
                              match uu____7971 with
                              | (l',uu____7980) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____7939
                      (FStar_Option.map
                         (fun uu____8013  ->
                            match uu____8013 with | (uu____8024,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____7934 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8065  ->
                          match uu____8065 with
                          | (l',uu____8074) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____8097 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____8097 with
      | (xxsym,xx) ->
          let uu____8102 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____8102 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               let uu____8109 =
                 let uu____8114 =
                   let uu____8115 =
                     let uu____8121 =
                       let uu____8122 =
                         let uu____8125 =
                           let uu____8126 =
                             let uu____8129 =
                               FStar_SMTEncoding_Util.mkApp ("PreType", [xx])
                                in
                             (tapp, uu____8129)  in
                           FStar_SMTEncoding_Util.mkEq uu____8126  in
                         (xx_has_type, uu____8125)  in
                       FStar_SMTEncoding_Util.mkImp uu____8122  in
                     ([[xx_has_type]],
                       ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                       (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                       uu____8121)
                      in
                   FStar_SMTEncoding_Util.mkForall uu____8115  in
                 let uu____8142 =
                   let uu____8144 =
                     let uu____8145 =
                       let uu____8146 = FStar_Util.digest_of_string tapp_hash
                          in
                       Prims.strcat "pretyping_" uu____8146  in
                     varops.mk_unique uu____8145  in
                   Some uu____8144  in
                 (uu____8114, (Some "pretyping"), uu____8142)  in
               FStar_SMTEncoding_Term.Assume uu____8109)
  
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
    let uu____8177 =
      let uu____8178 =
        let uu____8183 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8183, (Some "unit typing"), (Some "unit_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8178  in
    let uu____8186 =
      let uu____8188 =
        let uu____8189 =
          let uu____8194 =
            let uu____8195 =
              let uu____8201 =
                let uu____8202 =
                  let uu____8205 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8205)  in
                FStar_SMTEncoding_Util.mkImp uu____8202  in
              ([[typing_pred]], [xx], uu____8201)  in
            mkForall_fuel uu____8195  in
          (uu____8194, (Some "unit inversion"), (Some "unit_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8189  in
      [uu____8188]  in
    uu____8177 :: uu____8186  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8234 =
      let uu____8235 =
        let uu____8240 =
          let uu____8241 =
            let uu____8247 =
              let uu____8250 =
                let uu____8252 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8252]  in
              [uu____8250]  in
            let uu____8255 =
              let uu____8256 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8256 tt  in
            (uu____8247, [bb], uu____8255)  in
          FStar_SMTEncoding_Util.mkForall uu____8241  in
        (uu____8240, (Some "bool typing"), (Some "bool_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8235  in
    let uu____8268 =
      let uu____8270 =
        let uu____8271 =
          let uu____8276 =
            let uu____8277 =
              let uu____8283 =
                let uu____8284 =
                  let uu____8287 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8287)  in
                FStar_SMTEncoding_Util.mkImp uu____8284  in
              ([[typing_pred]], [xx], uu____8283)  in
            mkForall_fuel uu____8277  in
          (uu____8276, (Some "bool inversion"), (Some "bool_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8271  in
      [uu____8270]  in
    uu____8234 :: uu____8268  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8322 =
        let uu____8323 =
          let uu____8327 =
            let uu____8329 =
              let uu____8331 =
                let uu____8333 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8334 =
                  let uu____8336 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8336]  in
                uu____8333 :: uu____8334  in
              tt :: uu____8331  in
            tt :: uu____8329  in
          ("Prims.Precedes", uu____8327)  in
        FStar_SMTEncoding_Util.mkApp uu____8323  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8322  in
    let precedes_y_x =
      let uu____8339 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8339  in
    let uu____8341 =
      let uu____8342 =
        let uu____8347 =
          let uu____8348 =
            let uu____8354 =
              let uu____8357 =
                let uu____8359 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8359]  in
              [uu____8357]  in
            let uu____8362 =
              let uu____8363 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8363 tt  in
            (uu____8354, [bb], uu____8362)  in
          FStar_SMTEncoding_Util.mkForall uu____8348  in
        (uu____8347, (Some "int typing"), (Some "int_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8342  in
    let uu____8375 =
      let uu____8377 =
        let uu____8378 =
          let uu____8383 =
            let uu____8384 =
              let uu____8390 =
                let uu____8391 =
                  let uu____8394 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8394)  in
                FStar_SMTEncoding_Util.mkImp uu____8391  in
              ([[typing_pred]], [xx], uu____8390)  in
            mkForall_fuel uu____8384  in
          (uu____8383, (Some "int inversion"), (Some "int_inversion"))  in
        FStar_SMTEncoding_Term.Assume uu____8378  in
      let uu____8408 =
        let uu____8410 =
          let uu____8411 =
            let uu____8416 =
              let uu____8417 =
                let uu____8423 =
                  let uu____8424 =
                    let uu____8427 =
                      let uu____8428 =
                        let uu____8430 =
                          let uu____8432 =
                            let uu____8434 =
                              let uu____8435 =
                                let uu____8438 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8439 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8438, uu____8439)  in
                              FStar_SMTEncoding_Util.mkGT uu____8435  in
                            let uu____8440 =
                              let uu____8442 =
                                let uu____8443 =
                                  let uu____8446 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____8447 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____8446, uu____8447)  in
                                FStar_SMTEncoding_Util.mkGTE uu____8443  in
                              let uu____8448 =
                                let uu____8450 =
                                  let uu____8451 =
                                    let uu____8454 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____8455 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____8454, uu____8455)  in
                                  FStar_SMTEncoding_Util.mkLT uu____8451  in
                                [uu____8450]  in
                              uu____8442 :: uu____8448  in
                            uu____8434 :: uu____8440  in
                          typing_pred_y :: uu____8432  in
                        typing_pred :: uu____8430  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8428  in
                    (uu____8427, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8424  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8423)
                 in
              mkForall_fuel uu____8417  in
            (uu____8416, (Some "well-founded ordering on nat (alt)"),
              (Some "well-founded-ordering-on-nat"))
             in
          FStar_SMTEncoding_Term.Assume uu____8411  in
        [uu____8410]  in
      uu____8377 :: uu____8408  in
    uu____8341 :: uu____8375  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8486 =
      let uu____8487 =
        let uu____8492 =
          let uu____8493 =
            let uu____8499 =
              let uu____8502 =
                let uu____8504 = FStar_SMTEncoding_Term.boxString b  in
                [uu____8504]  in
              [uu____8502]  in
            let uu____8507 =
              let uu____8508 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8508 tt  in
            (uu____8499, [bb], uu____8507)  in
          FStar_SMTEncoding_Util.mkForall uu____8493  in
        (uu____8492, (Some "string typing"), (Some "string_typing"))  in
      FStar_SMTEncoding_Term.Assume uu____8487  in
    let uu____8520 =
      let uu____8522 =
        let uu____8523 =
          let uu____8528 =
            let uu____8529 =
              let uu____8535 =
                let uu____8536 =
                  let uu____8539 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____8539)  in
                FStar_SMTEncoding_Util.mkImp uu____8536  in
              ([[typing_pred]], [xx], uu____8535)  in
            mkForall_fuel uu____8529  in
          (uu____8528, (Some "string inversion"), (Some "string_inversion"))
           in
        FStar_SMTEncoding_Term.Assume uu____8523  in
      [uu____8522]  in
    uu____8486 :: uu____8520  in
  let mk_ref1 env reft_name uu____8562 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____8573 =
        let uu____8577 =
          let uu____8579 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____8579]
           in
        (reft_name, uu____8577)  in
      FStar_SMTEncoding_Util.mkApp uu____8573  in
    let refb =
      let uu____8582 =
        let uu____8586 =
          let uu____8588 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____8588]
           in
        (reft_name, uu____8586)  in
      FStar_SMTEncoding_Util.mkApp uu____8582  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____8592 =
      let uu____8593 =
        let uu____8598 =
          let uu____8599 =
            let uu____8605 =
              let uu____8606 =
                let uu____8609 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____8609)  in
              FStar_SMTEncoding_Util.mkImp uu____8606  in
            ([[typing_pred]], [xx; aa], uu____8605)  in
          mkForall_fuel uu____8599  in
        (uu____8598, (Some "ref inversion"), (Some "ref_inversion"))  in
      FStar_SMTEncoding_Term.Assume uu____8593  in
    let uu____8625 =
      let uu____8627 =
        let uu____8628 =
          let uu____8633 =
            let uu____8634 =
              let uu____8640 =
                let uu____8641 =
                  let uu____8644 =
                    FStar_SMTEncoding_Util.mkAnd (typing_pred, typing_pred_b)
                     in
                  let uu____8645 =
                    let uu____8646 =
                      let uu____8649 = FStar_SMTEncoding_Util.mkFreeV aa  in
                      let uu____8650 = FStar_SMTEncoding_Util.mkFreeV bb  in
                      (uu____8649, uu____8650)  in
                    FStar_SMTEncoding_Util.mkEq uu____8646  in
                  (uu____8644, uu____8645)  in
                FStar_SMTEncoding_Util.mkImp uu____8641  in
              ([[typing_pred; typing_pred_b]], [xx; aa; bb], uu____8640)  in
            mkForall_fuel' (Prims.parse_int "2") uu____8634  in
          (uu____8633, (Some "ref typing is injective"),
            (Some "ref_injectivity"))
           in
        FStar_SMTEncoding_Term.Assume uu____8628  in
      [uu____8627]  in
    uu____8592 :: uu____8625  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____8694 =
      let uu____8695 =
        let uu____8700 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____8700, (Some "False interpretation"), (Some "false_interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____8695  in
    [uu____8694]  in
  let mk_and_interp env conj uu____8712 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____8722 =
        let uu____8726 =
          let uu____8728 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
          [uu____8728]  in
        ("Valid", uu____8726)  in
      FStar_SMTEncoding_Util.mkApp uu____8722  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____8735 =
      let uu____8736 =
        let uu____8741 =
          let uu____8742 =
            let uu____8748 =
              let uu____8749 =
                let uu____8752 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____8752, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____8749  in
            ([[valid]], [aa; bb], uu____8748)  in
          FStar_SMTEncoding_Util.mkForall uu____8742  in
        (uu____8741, (Some "/\\ interpretation"), (Some "l_and-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____8736  in
    [uu____8735]  in
  let mk_or_interp env disj uu____8777 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____8787 =
        let uu____8791 =
          let uu____8793 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
          [uu____8793]  in
        ("Valid", uu____8791)  in
      FStar_SMTEncoding_Util.mkApp uu____8787  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____8800 =
      let uu____8801 =
        let uu____8806 =
          let uu____8807 =
            let uu____8813 =
              let uu____8814 =
                let uu____8817 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____8817, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____8814  in
            ([[valid]], [aa; bb], uu____8813)  in
          FStar_SMTEncoding_Util.mkForall uu____8807  in
        (uu____8806, (Some "\\/ interpretation"), (Some "l_or-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____8801  in
    [uu____8800]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let valid =
      let uu____8856 =
        let uu____8860 =
          let uu____8862 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])
             in
          [uu____8862]  in
        ("Valid", uu____8860)  in
      FStar_SMTEncoding_Util.mkApp uu____8856  in
    let uu____8865 =
      let uu____8866 =
        let uu____8871 =
          let uu____8872 =
            let uu____8878 =
              let uu____8879 =
                let uu____8882 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____8882, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____8879  in
            ([[valid]], [aa; xx1; yy1], uu____8878)  in
          FStar_SMTEncoding_Util.mkForall uu____8872  in
        (uu____8871, (Some "Eq2 interpretation"), (Some "eq2-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____8866  in
    [uu____8865]  in
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
      let uu____8927 =
        let uu____8931 =
          let uu____8933 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])
             in
          [uu____8933]  in
        ("Valid", uu____8931)  in
      FStar_SMTEncoding_Util.mkApp uu____8927  in
    let uu____8936 =
      let uu____8937 =
        let uu____8942 =
          let uu____8943 =
            let uu____8949 =
              let uu____8950 =
                let uu____8953 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____8953, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____8950  in
            ([[valid]], [aa; bb; xx1; yy1], uu____8949)  in
          FStar_SMTEncoding_Util.mkForall uu____8943  in
        (uu____8942, (Some "Eq3 interpretation"), (Some "eq3-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____8937  in
    [uu____8936]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____8992 =
        let uu____8996 =
          let uu____8998 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
          [uu____8998]  in
        ("Valid", uu____8996)  in
      FStar_SMTEncoding_Util.mkApp uu____8992  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9005 =
      let uu____9006 =
        let uu____9011 =
          let uu____9012 =
            let uu____9018 =
              let uu____9019 =
                let uu____9022 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9022, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9019  in
            ([[valid]], [aa; bb], uu____9018)  in
          FStar_SMTEncoding_Util.mkForall uu____9012  in
        (uu____9011, (Some "==> interpretation"), (Some "l_imp-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9006  in
    [uu____9005]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      let uu____9057 =
        let uu____9061 =
          let uu____9063 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
          [uu____9063]  in
        ("Valid", uu____9061)  in
      FStar_SMTEncoding_Util.mkApp uu____9057  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9070 =
      let uu____9071 =
        let uu____9076 =
          let uu____9077 =
            let uu____9083 =
              let uu____9084 =
                let uu____9087 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9087, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9084  in
            ([[valid]], [aa; bb], uu____9083)  in
          FStar_SMTEncoding_Util.mkForall uu____9077  in
        (uu____9076, (Some "<==> interpretation"), (Some "l_iff-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9071  in
    [uu____9070]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      let uu____9118 =
        let uu____9122 =
          let uu____9124 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
          [uu____9124]  in
        ("Valid", uu____9122)  in
      FStar_SMTEncoding_Util.mkApp uu____9118  in
    let not_valid_a =
      let uu____9128 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9128  in
    let uu____9130 =
      let uu____9131 =
        let uu____9136 =
          let uu____9137 =
            let uu____9143 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[valid]], [aa], uu____9143)  in
          FStar_SMTEncoding_Util.mkForall uu____9137  in
        (uu____9136, (Some "not interpretation"), (Some "l_not-interp"))  in
      FStar_SMTEncoding_Term.Assume uu____9131  in
    [uu____9130]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9180 =
        let uu____9184 =
          let uu____9186 = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])
             in
          [uu____9186]  in
        ("Valid", uu____9184)  in
      FStar_SMTEncoding_Util.mkApp uu____9180  in
    let valid_b_x =
      let uu____9190 =
        let uu____9194 =
          let uu____9196 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9196]  in
        ("Valid", uu____9194)  in
      FStar_SMTEncoding_Util.mkApp uu____9190  in
    let uu____9198 =
      let uu____9199 =
        let uu____9204 =
          let uu____9205 =
            let uu____9211 =
              let uu____9212 =
                let uu____9215 =
                  let uu____9216 =
                    let uu____9222 =
                      let uu____9225 =
                        let uu____9227 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9227]  in
                      [uu____9225]  in
                    let uu____9230 =
                      let uu____9231 =
                        let uu____9234 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9234, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9231  in
                    (uu____9222, [xx1], uu____9230)  in
                  FStar_SMTEncoding_Util.mkForall uu____9216  in
                (uu____9215, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9212  in
            ([[valid]], [aa; bb], uu____9211)  in
          FStar_SMTEncoding_Util.mkForall uu____9205  in
        (uu____9204, (Some "forall interpretation"), (Some "forall-interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____9199  in
    [uu____9198]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let valid =
      let uu____9282 =
        let uu____9286 =
          let uu____9288 = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])
             in
          [uu____9288]  in
        ("Valid", uu____9286)  in
      FStar_SMTEncoding_Util.mkApp uu____9282  in
    let valid_b_x =
      let uu____9292 =
        let uu____9296 =
          let uu____9298 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9298]  in
        ("Valid", uu____9296)  in
      FStar_SMTEncoding_Util.mkApp uu____9292  in
    let uu____9300 =
      let uu____9301 =
        let uu____9306 =
          let uu____9307 =
            let uu____9313 =
              let uu____9314 =
                let uu____9317 =
                  let uu____9318 =
                    let uu____9324 =
                      let uu____9327 =
                        let uu____9329 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9329]  in
                      [uu____9327]  in
                    let uu____9332 =
                      let uu____9333 =
                        let uu____9336 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9336, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9333  in
                    (uu____9324, [xx1], uu____9332)  in
                  FStar_SMTEncoding_Util.mkExists uu____9318  in
                (uu____9317, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9314  in
            ([[valid]], [aa; bb], uu____9313)  in
          FStar_SMTEncoding_Util.mkForall uu____9307  in
        (uu____9306, (Some "exists interpretation"), (Some "exists-interp"))
         in
      FStar_SMTEncoding_Term.Assume uu____9301  in
    [uu____9300]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9373 =
      let uu____9374 =
        let uu____9379 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9380 =
          let uu____9382 = varops.mk_unique "typing_range_const"  in
          Some uu____9382  in
        (uu____9379, (Some "Range_const typing"), uu____9380)  in
      FStar_SMTEncoding_Term.Assume uu____9374  in
    [uu____9373]  in
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
          let uu____9645 =
            FStar_Util.find_opt
              (fun uu____9663  ->
                 match uu____9663 with
                 | (l,uu____9673) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____9645 with
          | None  -> []
          | Some (uu____9695,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____9732 = encode_function_type_as_formula None None t env  in
        match uu____9732 with
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
            let uu____9765 =
              (let uu____9766 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm  in
               FStar_All.pipe_left Prims.op_Negation uu____9766) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____9765
            then
              let uu____9770 = new_term_constant_and_tok_from_lid env lid  in
              match uu____9770 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9782 =
                      let uu____9783 = FStar_Syntax_Subst.compress t_norm  in
                      uu____9783.FStar_Syntax_Syntax.n  in
                    match uu____9782 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9788) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9805  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9808 -> []  in
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
              (let uu____9817 = prims.is lid  in
               if uu____9817
               then
                 let vname = varops.new_fvar lid  in
                 let uu____9822 = prims.mk lid vname  in
                 match uu____9822 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____9837 =
                    let uu____9843 = curried_arrow_formals_comp t_norm  in
                    match uu____9843 with
                    | (args,comp) ->
                        if encode_non_total_function_typ
                        then
                          let uu____9858 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp
                             in
                          (args, uu____9858)
                        else
                          (let uu____9866 =
                             let uu____9870 =
                               FStar_TypeChecker_Env.result_typ env.tcenv
                                 comp
                                in
                             (None, uu____9870)  in
                           (args, uu____9866))
                     in
                  match uu____9837 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9886 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____9886 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9899 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_9923  ->
                                     match uu___124_9923 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9926 =
                                           FStar_Util.prefix vars  in
                                         (match uu____9926 with
                                          | (uu____9937,(xxsym,uu____9939))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____9949 =
                                                let uu____9950 =
                                                  let uu____9955 =
                                                    let uu____9956 =
                                                      let uu____9962 =
                                                        let uu____9963 =
                                                          let uu____9966 =
                                                            let uu____9967 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9967
                                                             in
                                                          (vapp, uu____9966)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9963
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____9962)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9956
                                                     in
                                                  (uu____9955,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "disc_equation_"
                                                          (escape
                                                             d.FStar_Ident.str))))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____9950
                                                 in
                                              [uu____9949])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9979 =
                                           FStar_Util.prefix vars  in
                                         (match uu____9979 with
                                          | (uu____9990,(xxsym,uu____9992))
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
                                              let uu____10006 =
                                                let uu____10007 =
                                                  let uu____10012 =
                                                    let uu____10013 =
                                                      let uu____10019 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10019)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10013
                                                     in
                                                  (uu____10012,
                                                    (Some
                                                       "Projector equation"),
                                                    (Some
                                                       (Prims.strcat
                                                          "proj_equation_"
                                                          tp_name)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____10007
                                                 in
                                              [uu____10006])
                                     | uu____10029 -> []))
                              in
                           let uu____10030 = encode_binders None formals env1
                              in
                           (match uu____10030 with
                            | (vars,guards,env',decls1,uu____10046) ->
                                let uu____10053 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10058 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10058, decls1)
                                  | Some p ->
                                      let uu____10060 = encode_formula p env'
                                         in
                                      (match uu____10060 with
                                       | (g,ds) ->
                                           let uu____10067 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10067,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10053 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10076 =
                                         let uu____10080 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10080)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10076
                                        in
                                     let uu____10085 =
                                       let vname_decl =
                                         let uu____10090 =
                                           let uu____10096 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10101  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10096,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10090
                                          in
                                       let uu____10106 =
                                         let env2 =
                                           let uu___152_10110 = env1  in
                                           {
                                             bindings =
                                               (uu___152_10110.bindings);
                                             depth = (uu___152_10110.depth);
                                             tcenv = (uu___152_10110.tcenv);
                                             warn = (uu___152_10110.warn);
                                             cache = (uu___152_10110.cache);
                                             nolabels =
                                               (uu___152_10110.nolabels);
                                             use_zfuel_name =
                                               (uu___152_10110.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____10111 =
                                           let uu____10112 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10112  in
                                         if uu____10111
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10106 with
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
                                           let uu____10124 =
                                             match formals with
                                             | [] ->
                                                 let uu____10133 =
                                                   let uu____10134 =
                                                     let uu____10136 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10136
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10134
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10133)
                                             | uu____10139 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10144 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10144
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10146 =
                                                     let uu____10151 =
                                                       let uu____10152 =
                                                         let uu____10158 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10158)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10152
                                                        in
                                                     (uu____10151,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Some
                                                          (Prims.strcat
                                                             "token_correspondence_"
                                                             vname)))
                                                      in
                                                   FStar_SMTEncoding_Term.Assume
                                                     uu____10146
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10124 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10085 with
                                      | (decls2,env2) ->
                                          let uu____10183 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10188 =
                                              encode_term res_t1 env'  in
                                            match uu____10188 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10196 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10196,
                                                  decls)
                                             in
                                          (match uu____10183 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10204 =
                                                   let uu____10209 =
                                                     let uu____10210 =
                                                       let uu____10216 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10216)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10210
                                                      in
                                                   (uu____10209,
                                                     (Some "free var typing"),
                                                     (Some
                                                        (Prims.strcat
                                                           "typing_" vname)))
                                                    in
                                                 FStar_SMTEncoding_Term.Assume
                                                   uu____10204
                                                  in
                                               let freshness =
                                                 let uu____10226 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10226
                                                 then
                                                   let uu____10229 =
                                                     let uu____10230 =
                                                       let uu____10236 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd)
                                                          in
                                                       let uu____10242 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10236,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10242)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10230
                                                      in
                                                   let uu____10244 =
                                                     let uu____10246 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [uu____10246]  in
                                                   uu____10229 :: uu____10244
                                                 else []  in
                                               let g =
                                                 let uu____10250 =
                                                   let uu____10252 =
                                                     let uu____10254 =
                                                       let uu____10256 =
                                                         let uu____10258 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10258
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10256
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10254
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10252
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10250
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
          let uu____10280 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10280 with
          | None  ->
              let uu____10303 = encode_free_var env x t t_norm []  in
              (match uu____10303 with
               | (decls,env1) ->
                   let uu____10318 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10318 with
                    | (n1,x',uu____10337) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10349) -> ((n1, x1), [], env)
  
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
          let uu____10382 = encode_free_var env lid t tt quals  in
          match uu____10382 with
          | (decls,env1) ->
              let uu____10393 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10393
              then
                let uu____10397 =
                  let uu____10399 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10399  in
                (uu____10397, env1)
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
             (fun uu____10427  ->
                fun lb  ->
                  match uu____10427 with
                  | (decls,env1) ->
                      let uu____10439 =
                        let uu____10443 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10443
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10439 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10467  ->
      fun quals  ->
        match uu____10467 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____10516 = FStar_Util.first_N nbinders formals  in
              match uu____10516 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10556  ->
                         fun uu____10557  ->
                           match (uu____10556, uu____10557) with
                           | ((formal,uu____10567),(binder,uu____10569)) ->
                               let uu____10574 =
                                 let uu____10579 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____10579)  in
                               FStar_Syntax_Syntax.NT uu____10574) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____10584 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10598  ->
                              match uu____10598 with
                              | (x,i) ->
                                  let uu____10605 =
                                    let uu___153_10606 = x  in
                                    let uu____10607 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___153_10606.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___153_10606.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10607
                                    }  in
                                  (uu____10605, i)))
                       in
                    FStar_All.pipe_right uu____10584
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____10619 =
                      let uu____10621 =
                        let uu____10622 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____10622.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10621
                       in
                    let uu____10626 =
                      let uu____10627 = FStar_Syntax_Subst.compress body  in
                      let uu____10628 =
                        let uu____10629 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left Prims.snd uu____10629  in
                      FStar_Syntax_Syntax.extend_app_n uu____10627
                        uu____10628
                       in
                    uu____10626 uu____10619 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let rec aux norm1 t_norm1 =
                let uu____10686 = FStar_Syntax_Util.abs_formals e  in
                match uu____10686 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10735::uu____10736 ->
                         let uu____10744 =
                           let uu____10745 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____10745.FStar_Syntax_Syntax.n  in
                         (match uu____10744 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10772 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____10772 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres =
                                     FStar_TypeChecker_Env.result_typ
                                       env.tcenv c1
                                      in
                                   let uu____10798 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____10798
                                   then
                                     let uu____10816 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____10816 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10862  ->
                                                   fun uu____10863  ->
                                                     match (uu____10862,
                                                             uu____10863)
                                                     with
                                                     | ((b,uu____10873),
                                                        (x,uu____10875)) ->
                                                         let uu____10880 =
                                                           let uu____10885 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           (b, uu____10885)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10880) bs0
                                                formals1
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____10887 =
                                            let uu____10898 =
                                              FStar_TypeChecker_Env.result_typ
                                                env.tcenv c2
                                               in
                                            (bs0, body1, bs0, uu____10898)
                                             in
                                          (uu____10887, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____10933 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____10933 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____10985) ->
                              let uu____10990 =
                                let uu____11001 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                Prims.fst uu____11001  in
                              (uu____10990, true)
                          | uu____11034 when Prims.op_Negation norm1 ->
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
                          | uu____11036 ->
                              let uu____11037 =
                                let uu____11038 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11039 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11038
                                  uu____11039
                                 in
                              failwith uu____11037)
                     | uu____11052 ->
                         let uu____11053 =
                           let uu____11054 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11054.FStar_Syntax_Syntax.n  in
                         (match uu____11053 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11081 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11081 with
                               | (formals1,c1) ->
                                   let tres =
                                     FStar_TypeChecker_Env.result_typ
                                       env.tcenv c1
                                      in
                                   let uu____11099 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11099 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11147 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11175 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp))
                  in
               if uu____11175
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11182 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11223  ->
                            fun lb  ->
                              match uu____11223 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11274 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11274
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11277 =
                                      let uu____11285 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11285
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11277 with
                                    | (tok,decl,env2) ->
                                        let uu____11310 =
                                          let uu____11317 =
                                            let uu____11323 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11323, tok)  in
                                          uu____11317 :: toks  in
                                        (uu____11310, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11182 with
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
                        | uu____11425 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11430 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11430 vars)
                            else
                              (let uu____11432 =
                                 let uu____11436 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11436)  in
                               FStar_SMTEncoding_Util.mkApp uu____11432)
                         in
                      let uu____11441 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_11443  ->
                                 match uu___125_11443 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11444 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11447 =
                                     FStar_Syntax_Util.is_pure_or_ghost_function
                                       t
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11447)))
                         in
                      if uu____11441
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11467;
                                FStar_Syntax_Syntax.lbunivs = uu____11468;
                                FStar_Syntax_Syntax.lbtyp = uu____11469;
                                FStar_Syntax_Syntax.lbeff = uu____11470;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let e1 = FStar_Syntax_Subst.compress e  in
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____11512 =
                                 destruct_bound_function flid t_norm e1  in
                               (match uu____11512 with
                                | ((binders,body,uu____11524,uu____11525),curry)
                                    ->
                                    let uu____11531 =
                                      encode_binders None binders env1  in
                                    (match uu____11531 with
                                     | (vars,guards,env',binder_decls,uu____11547)
                                         ->
                                         let app = mk_app1 curry f ftok vars
                                            in
                                         let uu____11555 =
                                           let uu____11560 =
                                             FStar_All.pipe_right quals
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Logic)
                                              in
                                           if uu____11560
                                           then
                                             let uu____11566 =
                                               FStar_SMTEncoding_Term.mk_Valid
                                                 app
                                                in
                                             let uu____11567 =
                                               encode_formula body env'  in
                                             (uu____11566, uu____11567)
                                           else
                                             (let uu____11573 =
                                                encode_term body env'  in
                                              (app, uu____11573))
                                            in
                                         (match uu____11555 with
                                          | (app1,(body1,decls2)) ->
                                              let eqn =
                                                let uu____11587 =
                                                  let uu____11592 =
                                                    let uu____11593 =
                                                      let uu____11599 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (app1, body1)
                                                         in
                                                      ([[app1]], vars,
                                                        uu____11599)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11593
                                                     in
                                                  let uu____11605 =
                                                    let uu____11607 =
                                                      FStar_Util.format1
                                                        "Equation for %s"
                                                        flid.FStar_Ident.str
                                                       in
                                                    Some uu____11607  in
                                                  (uu____11592, uu____11605,
                                                    (Some
                                                       (Prims.strcat
                                                          "equation_" f)))
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  uu____11587
                                                 in
                                              let uu____11610 =
                                                let uu____11612 =
                                                  let uu____11614 =
                                                    let uu____11616 =
                                                      let uu____11618 =
                                                        primitive_type_axioms
                                                          env1.tcenv flid f
                                                          app1
                                                         in
                                                      FStar_List.append 
                                                        [eqn] uu____11618
                                                       in
                                                    FStar_List.append decls2
                                                      uu____11616
                                                     in
                                                  FStar_List.append
                                                    binder_decls uu____11614
                                                   in
                                                FStar_List.append decls1
                                                  uu____11612
                                                 in
                                              (uu____11610, env1))))
                           | uu____11621 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11640 = varops.fresh "fuel"  in
                             (uu____11640, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____11643 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11682  ->
                                     fun uu____11683  ->
                                       match (uu____11682, uu____11683) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____11765 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____11765  in
                                           let gtok =
                                             let uu____11767 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____11767  in
                                           let env3 =
                                             let uu____11769 =
                                               let uu____11771 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11771
                                                in
                                             push_free_var env2 flid gtok
                                               uu____11769
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____11643 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____11855
                                 t_norm uu____11857 =
                                 match (uu____11855, uu____11857) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uu____11881;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____11882;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____11883;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     ((let uu____11901 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug
                                              env01.tcenv)
                                           (FStar_Options.Other "SMTEncoding")
                                          in
                                       if uu____11901
                                       then
                                         let uu____11902 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lbn
                                            in
                                         let uu____11903 =
                                           FStar_Syntax_Print.term_to_string
                                             t_norm
                                            in
                                         let uu____11904 =
                                           FStar_Syntax_Print.term_to_string
                                             e
                                            in
                                         FStar_Util.print3
                                           "Encoding let rec %s : %s = %s\n"
                                           uu____11902 uu____11903
                                           uu____11904
                                       else ());
                                      (let uu____11906 =
                                         destruct_bound_function flid t_norm
                                           e
                                          in
                                       match uu____11906 with
                                       | ((binders,body,formals,tres),curry)
                                           ->
                                           ((let uu____11928 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env01.tcenv)
                                                 (FStar_Options.Other
                                                    "SMTEncoding")
                                                in
                                             if uu____11928
                                             then
                                               let uu____11929 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   ", " binders
                                                  in
                                               let uu____11930 =
                                                 FStar_Syntax_Print.term_to_string
                                                   body
                                                  in
                                               FStar_Util.print2
                                                 "Encoding let rec: binders=[%s], body=%s\n"
                                                 uu____11929 uu____11930
                                             else ());
                                            if curry
                                            then
                                              failwith
                                                "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                            else ();
                                            (let uu____11934 =
                                               encode_binders None binders
                                                 env2
                                                in
                                             match uu____11934 with
                                             | (vars,guards,env',binder_decls,uu____11952)
                                                 ->
                                                 let decl_g =
                                                   let uu____11960 =
                                                     let uu____11966 =
                                                       let uu____11968 =
                                                         FStar_List.map
                                                           Prims.snd vars
                                                          in
                                                       FStar_SMTEncoding_Term.Fuel_sort
                                                         :: uu____11968
                                                        in
                                                     (g, uu____11966,
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       (Some
                                                          "Fuel-instrumented function name"))
                                                      in
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     uu____11960
                                                    in
                                                 let env02 =
                                                   push_zfuel_name env01 flid
                                                     g
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
                                                   let uu____11983 =
                                                     let uu____11987 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         vars
                                                        in
                                                     (f, uu____11987)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____11983
                                                    in
                                                 let gsapp =
                                                   let uu____11993 =
                                                     let uu____11997 =
                                                       let uu____11999 =
                                                         FStar_SMTEncoding_Util.mkApp
                                                           ("SFuel",
                                                             [fuel_tm])
                                                          in
                                                       uu____11999 :: vars_tm
                                                        in
                                                     (g, uu____11997)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____11993
                                                    in
                                                 let gmax =
                                                   let uu____12003 =
                                                     let uu____12007 =
                                                       let uu____12009 =
                                                         FStar_SMTEncoding_Util.mkApp
                                                           ("MaxFuel", [])
                                                          in
                                                       uu____12009 :: vars_tm
                                                        in
                                                     (g, uu____12007)  in
                                                   FStar_SMTEncoding_Util.mkApp
                                                     uu____12003
                                                    in
                                                 let uu____12012 =
                                                   encode_term body env'  in
                                                 (match uu____12012 with
                                                  | (body_tm,decls2) ->
                                                      let eqn_g =
                                                        let uu____12023 =
                                                          let uu____12028 =
                                                            let uu____12029 =
                                                              let uu____12037
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
                                                                uu____12037)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall'
                                                              uu____12029
                                                             in
                                                          let uu____12048 =
                                                            let uu____12050 =
                                                              FStar_Util.format1
                                                                "Equation for fuel-instrumented recursive function: %s"
                                                                flid.FStar_Ident.str
                                                               in
                                                            Some uu____12050
                                                             in
                                                          (uu____12028,
                                                            uu____12048,
                                                            (Some
                                                               (Prims.strcat
                                                                  "equation_with_fuel_"
                                                                  g)))
                                                           in
                                                        FStar_SMTEncoding_Term.Assume
                                                          uu____12023
                                                         in
                                                      let eqn_f =
                                                        let uu____12054 =
                                                          let uu____12059 =
                                                            let uu____12060 =
                                                              let uu____12066
                                                                =
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  (app, gmax)
                                                                 in
                                                              ([[app]], vars,
                                                                uu____12066)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall
                                                              uu____12060
                                                             in
                                                          (uu____12059,
                                                            (Some
                                                               "Correspondence of recursive function to instrumented version"),
                                                            (Some
                                                               (Prims.strcat
                                                                  "fuel_correspondence_"
                                                                  g)))
                                                           in
                                                        FStar_SMTEncoding_Term.Assume
                                                          uu____12054
                                                         in
                                                      let eqn_g' =
                                                        let uu____12075 =
                                                          let uu____12080 =
                                                            let uu____12081 =
                                                              let uu____12087
                                                                =
                                                                let uu____12088
                                                                  =
                                                                  let uu____12091
                                                                    =
                                                                    let uu____12092
                                                                    =
                                                                    let uu____12096
                                                                    =
                                                                    let uu____12098
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12098
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12096)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12092
                                                                     in
                                                                  (gsapp,
                                                                    uu____12091)
                                                                   in
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  uu____12088
                                                                 in
                                                              ([[gsapp]],
                                                                (fuel ::
                                                                vars),
                                                                uu____12087)
                                                               in
                                                            FStar_SMTEncoding_Util.mkForall
                                                              uu____12081
                                                             in
                                                          (uu____12080,
                                                            (Some
                                                               "Fuel irrelevance"),
                                                            (Some
                                                               (Prims.strcat
                                                                  "fuel_irrelevance_"
                                                                  g)))
                                                           in
                                                        FStar_SMTEncoding_Term.Assume
                                                          uu____12075
                                                         in
                                                      let uu____12111 =
                                                        let uu____12116 =
                                                          encode_binders None
                                                            formals env02
                                                           in
                                                        match uu____12116
                                                        with
                                                        | (vars1,v_guards,env3,binder_decls1,uu____12133)
                                                            ->
                                                            let vars_tm1 =
                                                              FStar_List.map
                                                                FStar_SMTEncoding_Util.mkFreeV
                                                                vars1
                                                               in
                                                            let gapp =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (g, (fuel_tm
                                                                  ::
                                                                  vars_tm1))
                                                               in
                                                            let tok_corr =
                                                              let tok_app =
                                                                let uu____12148
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                   in
                                                                mk_Apply
                                                                  uu____12148
                                                                  (fuel ::
                                                                  vars1)
                                                                 in
                                                              let uu____12151
                                                                =
                                                                let uu____12156
                                                                  =
                                                                  let uu____12157
                                                                    =
                                                                    let uu____12163
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12163)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    uu____12157
                                                                   in
                                                                (uu____12156,
                                                                  (Some
                                                                    "Fuel token correspondence"),
                                                                  (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)))
                                                                 in
                                                              FStar_SMTEncoding_Term.Assume
                                                                uu____12151
                                                               in
                                                            let uu____12175 =
                                                              let uu____12179
                                                                =
                                                                encode_term_pred
                                                                  None tres
                                                                  env3 gapp
                                                                 in
                                                              match uu____12179
                                                              with
                                                              | (g_typing,d3)
                                                                  ->
                                                                  let uu____12187
                                                                    =
                                                                    let uu____12189
                                                                    =
                                                                    let uu____12190
                                                                    =
                                                                    let uu____12195
                                                                    =
                                                                    let uu____12196
                                                                    =
                                                                    let uu____12202
                                                                    =
                                                                    let uu____12203
                                                                    =
                                                                    let uu____12206
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12206,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12203
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12202)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12196
                                                                     in
                                                                    (uu____12195,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)))  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____12190
                                                                     in
                                                                    [uu____12189]
                                                                     in
                                                                  (d3,
                                                                    uu____12187)
                                                               in
                                                            (match uu____12175
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
                                                      (match uu____12111 with
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
                                                             env02)))))))
                                  in
                               let uu____12242 =
                                 let uu____12249 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12281  ->
                                      fun uu____12282  ->
                                        match (uu____12281, uu____12282) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12358 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12358 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12249
                                  in
                               (match uu____12242 with
                                | (decls2,eqns,env01) ->
                                    let uu____12398 =
                                      let uu____12403 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____12403
                                        (FStar_List.partition
                                           (fun uu___126_12413  ->
                                              match uu___126_12413 with
                                              | FStar_SMTEncoding_Term.DeclFun
                                                  uu____12414 -> true
                                              | uu____12420 -> false))
                                       in
                                    (match uu____12398 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12438 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____12438
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
      (let uu____12471 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____12471
       then
         let uu____12472 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
           uu____12472
       else ());
      (let nm =
         let uu____12475 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____12475 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____12478 = encode_sigelt' env se  in
       match uu____12478 with
       | (g,e) ->
           (match g with
            | [] ->
                let uu____12487 =
                  let uu____12489 =
                    let uu____12490 = FStar_Util.format1 "<Skipped %s/>" nm
                       in
                    FStar_SMTEncoding_Term.Caption uu____12490  in
                  [uu____12489]  in
                (uu____12487, e)
            | uu____12492 ->
                let uu____12493 =
                  let uu____12495 =
                    let uu____12497 =
                      let uu____12498 =
                        FStar_Util.format1 "<Start encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12498  in
                    uu____12497 :: g  in
                  let uu____12499 =
                    let uu____12501 =
                      let uu____12502 =
                        FStar_Util.format1 "</end encoding %s>" nm  in
                      FStar_SMTEncoding_Term.Caption uu____12502  in
                    [uu____12501]  in
                  FStar_List.append uu____12495 uu____12499  in
                (uu____12493, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12510 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____12521) ->
          let uu____12522 =
            let uu____12523 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____12523 Prims.op_Negation  in
          if uu____12522
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12543 ->
                   let uu____12544 =
                     let uu____12547 =
                       let uu____12548 =
                         let uu____12563 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12563)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____12548  in
                     FStar_Syntax_Syntax.mk uu____12547  in
                   uu____12544 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____12616 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____12616 with
               | (aname,atok,env2) ->
                   let uu____12626 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____12626 with
                    | (formals,uu____12636) ->
                        let uu____12643 =
                          let uu____12646 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____12646 env2  in
                        (match uu____12643 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12654 =
                                 let uu____12655 =
                                   let uu____12661 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12669  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____12661,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____12655
                                  in
                               [uu____12654;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____12676 =
                               let uu____12683 =
                                 FStar_All.pipe_right formals
                                   (FStar_List.map
                                      (fun uu____12703  ->
                                         match uu____12703 with
                                         | (bv,uu____12711) ->
                                             let uu____12712 =
                                               gen_term_var env2 bv  in
                                             (match uu____12712 with
                                              | (xxsym,xx,uu____12722) ->
                                                  ((xxsym,
                                                     FStar_SMTEncoding_Term.Term_sort),
                                                    xx))))
                                  in
                               FStar_All.pipe_right uu____12683
                                 FStar_List.split
                                in
                             (match uu____12676 with
                              | (xs_sorts,xs) ->
                                  let app =
                                    let uu____12752 =
                                      let uu____12756 =
                                        let uu____12758 =
                                          FStar_SMTEncoding_Util.mkApp
                                            (aname, xs)
                                           in
                                        [uu____12758]  in
                                      ("Reify", uu____12756)  in
                                    FStar_SMTEncoding_Util.mkApp uu____12752
                                     in
                                  let a_eq =
                                    let uu____12762 =
                                      let uu____12767 =
                                        let uu____12768 =
                                          let uu____12774 =
                                            let uu____12775 =
                                              let uu____12778 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____12778)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12775
                                             in
                                          ([[app]], xs_sorts, uu____12774)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12768
                                         in
                                      (uu____12767, (Some "Action equality"),
                                        (Some
                                           (Prims.strcat aname "_equality")))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____12762
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____12791 =
                                      let uu____12796 =
                                        let uu____12797 =
                                          let uu____12803 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____12803)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12797
                                         in
                                      (uu____12796,
                                        (Some "Action token correspondence"),
                                        (Some
                                           (Prims.strcat aname
                                              "_token_correspondence")))
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____12791
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____12814 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____12814 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____12830,uu____12831,uu____12832,uu____12833) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____12836 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____12836 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____12847,t,quals,uu____12850) ->
          let will_encode_definition =
            let uu____12854 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___127_12856  ->
                      match uu___127_12856 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12859 -> false))
               in
            Prims.op_Negation uu____12854  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____12865 = encode_top_level_val env fv t quals  in
             match uu____12865 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____12877 =
                   let uu____12879 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____12879  in
                 (uu____12877, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____12884,uu____12885) ->
          let uu____12888 = encode_formula f env  in
          (match uu____12888 with
           | (f1,decls) ->
               let g =
                 let uu____12897 =
                   let uu____12898 =
                     let uu____12903 =
                       let uu____12905 =
                         let uu____12906 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____12906  in
                       Some uu____12905  in
                     let uu____12907 =
                       let uu____12909 =
                         varops.mk_unique
                           (Prims.strcat "assumption_" l.FStar_Ident.str)
                          in
                       Some uu____12909  in
                     (f1, uu____12903, uu____12907)  in
                   FStar_SMTEncoding_Term.Assume uu____12898  in
                 [uu____12897]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____12915,quals,uu____12917)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____12925 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____12932 =
                       let uu____12937 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____12937.FStar_Syntax_Syntax.fv_name  in
                     uu____12932.FStar_Syntax_Syntax.v  in
                   let uu____12941 =
                     let uu____12942 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____12942  in
                   if uu____12941
                   then
                     let val_decl =
                       FStar_Syntax_Syntax.Sig_declare_typ
                         (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp), quals, r)
                        in
                     let uu____12961 = encode_sigelt' env1 val_decl  in
                     match uu____12961 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs)
             in
          (match uu____12925 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____12978,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____12980;
                          FStar_Syntax_Syntax.lbtyp = uu____12981;
                          FStar_Syntax_Syntax.lbeff = uu____12982;
                          FStar_Syntax_Syntax.lbdef = uu____12983;_}::[]),uu____12984,uu____12985,uu____12986,uu____12987)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13003 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13003 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 let uu____13021 =
                   let uu____13025 =
                     let uu____13027 =
                       FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                     [uu____13027]  in
                   ("Valid", uu____13025)  in
                 FStar_SMTEncoding_Util.mkApp uu____13021  in
               let decls =
                 let uu____13032 =
                   let uu____13034 =
                     let uu____13035 =
                       let uu____13040 =
                         let uu____13041 =
                           let uu____13047 =
                             let uu____13048 =
                               let uu____13051 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13051)  in
                             FStar_SMTEncoding_Util.mkEq uu____13048  in
                           ([[valid_b2t_x]], [xx], uu____13047)  in
                         FStar_SMTEncoding_Util.mkForall uu____13041  in
                       (uu____13040, (Some "b2t def"), (Some "b2t_def"))  in
                     FStar_SMTEncoding_Term.Assume uu____13035  in
                   [uu____13034]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13032
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13069,uu____13070,uu____13071,quals,uu____13073) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13081  ->
                  match uu___128_13081 with
                  | FStar_Syntax_Syntax.Discriminator uu____13082 -> true
                  | uu____13083 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____13085,uu____13086,lids,quals,uu____13089) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13098 =
                     let uu____13099 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13099.FStar_Ident.idText  in
                   uu____13098 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13101  ->
                     match uu___129_13101 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13102 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13105,uu____13106,quals,uu____13108) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13120  ->
                  match uu___130_13120 with
                  | FStar_Syntax_Syntax.Projector uu____13121 -> true
                  | uu____13124 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13131 = try_lookup_free_var env l  in
          (match uu____13131 with
           | Some uu____13135 -> ([], env)
           | None  ->
               let se1 =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l))
                  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13143,uu____13144,quals,uu____13146) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let uu____13158 =
            let uu____13159 =
              FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef  in
            uu____13159.FStar_Syntax_Syntax.n  in
          (match uu____13158 with
           | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____13166) ->
               let body1 = FStar_Syntax_Util.mk_reify body  in
               let tm =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_abs (bs, body1, None))) None
                   (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos
                  in
               let tm' =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Reify;
                   FStar_TypeChecker_Normalize.Eager_unfolding;
                   FStar_TypeChecker_Normalize.EraseUniverses;
                   FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                   env.tcenv tm
                  in
               let lb_typ =
                 let uu____13221 =
                   FStar_Syntax_Util.arrow_formals_comp
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 match uu____13221 with
                 | (formals,comp) ->
                     let reified_typ =
                       let uu____13236 =
                         FStar_TypeChecker_Env.lcomp_of_comp env.tcenv comp
                          in
                       FStar_TypeChecker_Util.reify_comp
                         (let uu___156_13237 = env.tcenv  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___156_13237.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___156_13237.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___156_13237.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___156_13237.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___156_13237.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___156_13237.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___156_13237.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___156_13237.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___156_13237.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___156_13237.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___156_13237.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___156_13237.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___156_13237.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___156_13237.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___156_13237.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___156_13237.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___156_13237.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___156_13237.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___156_13237.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___156_13237.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___156_13237.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___156_13237.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___156_13237.FStar_TypeChecker_Env.qname_and_index)
                          }) uu____13236
                        in
                     let uu____13238 =
                       FStar_Syntax_Syntax.mk_Total reified_typ  in
                     FStar_Syntax_Util.arrow formals uu____13238
                  in
               let lb1 =
                 let uu___157_13240 = lb  in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___157_13240.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___157_13240.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = lb_typ;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___157_13240.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef = tm'
                 }  in
               encode_top_level_let env (false, [lb1]) quals
           | uu____13242 -> ([], env))
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13246,uu____13247,quals,uu____13249) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____13263,uu____13264,uu____13265) ->
          let uu____13272 = encode_signature env ses  in
          (match uu____13272 with
           | (g,env1) ->
               let uu____13282 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13292  ->
                         match uu___131_13292 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13293,Some "inversion axiom",uu____13294)
                             -> false
                         | uu____13298 -> true))
                  in
               (match uu____13282 with
                | (g',inversions) ->
                    let uu____13307 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13317  ->
                              match uu___132_13317 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13318 ->
                                  true
                              | uu____13324 -> false))
                       in
                    (match uu____13307 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13335,tps,k,uu____13338,datas,quals,uu____13341) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13350  ->
                    match uu___133_13350 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13351 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13358 = c  in
              match uu____13358 with
              | (name,args,uu____13362,uu____13363,uu____13364) ->
                  let uu____13367 =
                    let uu____13368 =
                      let uu____13374 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13381  ->
                                match uu____13381 with
                                | (uu____13385,sort,uu____13387) -> sort))
                         in
                      (name, uu____13374, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13368  in
                  [uu____13367]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13405 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13408 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13408 FStar_Option.isNone))
               in
            if uu____13405
            then []
            else
              (let uu____13419 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13419 with
               | (xxsym,xx) ->
                   let uu____13425 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13436  ->
                             fun l  ->
                               match uu____13436 with
                               | (out,decls) ->
                                   let uu____13448 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13448 with
                                    | (uu____13454,data_t) ->
                                        let uu____13456 =
                                          FStar_TypeChecker_Util.arrow_formals
                                            env.tcenv data_t
                                           in
                                        (match uu____13456 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13470 =
                                                 let uu____13471 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____13471.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____13470 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13479,indices) ->
                                                   indices
                                               | uu____13495 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13504  ->
                                                         match uu____13504
                                                         with
                                                         | (x,uu____13508) ->
                                                             let uu____13509
                                                               =
                                                               let uu____13510
                                                                 =
                                                                 let uu____13514
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____13514,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13510
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____13509)
                                                    env)
                                                in
                                             let uu____13516 =
                                               encode_args indices env1  in
                                             (match uu____13516 with
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
                                                      let uu____13536 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13544
                                                                 =
                                                                 let uu____13547
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____13547,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13544)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____13536
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____13549 =
                                                      let uu____13550 =
                                                        let uu____13553 =
                                                          let uu____13554 =
                                                            let uu____13557 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____13557,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13554
                                                           in
                                                        (out, uu____13553)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13550
                                                       in
                                                    (uu____13549,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13425 with
                    | (data_ax,decls) ->
                        let uu____13565 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____13565 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13576 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13576 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____13579 =
                                 let uu____13584 =
                                   let uu____13585 =
                                     let uu____13591 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____13599 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____13591,
                                       uu____13599)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13585
                                    in
                                 let uu____13607 =
                                   let uu____13609 =
                                     varops.mk_unique
                                       (Prims.strcat
                                          "fuel_guarded_inversion_"
                                          t.FStar_Ident.str)
                                      in
                                   Some uu____13609  in
                                 (uu____13584, (Some "inversion axiom"),
                                   uu____13607)
                                  in
                               FStar_SMTEncoding_Term.Assume uu____13579  in
                             let pattern_guarded_inversion =
                               let uu____13614 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____13614
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____13622 =
                                   let uu____13623 =
                                     let uu____13628 =
                                       let uu____13629 =
                                         let uu____13635 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____13643 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13635, uu____13643)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13629
                                        in
                                     let uu____13651 =
                                       let uu____13653 =
                                         varops.mk_unique
                                           (Prims.strcat
                                              "pattern_guarded_inversion_"
                                              t.FStar_Ident.str)
                                          in
                                       Some uu____13653  in
                                     (uu____13628, (Some "inversion axiom"),
                                       uu____13651)
                                      in
                                   FStar_SMTEncoding_Term.Assume uu____13623
                                    in
                                 [uu____13622]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____13657 =
            let uu____13663 =
              let uu____13664 = FStar_Syntax_Subst.compress k  in
              uu____13664.FStar_Syntax_Syntax.n  in
            match uu____13663 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                let uu____13684 =
                  FStar_TypeChecker_Env.result_typ env.tcenv kres  in
                ((FStar_List.append tps formals), uu____13684)
            | uu____13690 -> (tps, k)  in
          (match uu____13657 with
           | (formals,res) ->
               let uu____13701 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____13701 with
                | (formals1,res1) ->
                    let uu____13708 = encode_binders None formals1 env  in
                    (match uu____13708 with
                     | (vars,guards,env',binder_decls,uu____13723) ->
                         let uu____13730 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____13730 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____13743 =
                                  let uu____13747 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____13747)  in
                                FStar_SMTEncoding_Util.mkApp uu____13743  in
                              let uu____13752 =
                                let tname_decl =
                                  let uu____13758 =
                                    let uu____13759 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13774  ->
                                              match uu____13774 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____13782 = varops.next_id ()  in
                                    (tname, uu____13759,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13782, false)
                                     in
                                  constructor_or_logic_type_decl uu____13758
                                   in
                                let uu____13787 =
                                  match vars with
                                  | [] ->
                                      let uu____13794 =
                                        let uu____13795 =
                                          let uu____13797 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13797
                                           in
                                        push_free_var env1 t tname
                                          uu____13795
                                         in
                                      ([], uu____13794)
                                  | uu____13801 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____13807 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13807
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____13816 =
                                          let uu____13821 =
                                            let uu____13822 =
                                              let uu____13830 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____13830)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13822
                                             in
                                          (uu____13821,
                                            (Some "name-token correspondence"),
                                            (Some
                                               (Prims.strcat
                                                  "token_correspondence_"
                                                  ttok)))
                                           in
                                        FStar_SMTEncoding_Term.Assume
                                          uu____13816
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____13787 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____13752 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13854 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____13854 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13868 =
                                               let uu____13869 =
                                                 let uu____13874 =
                                                   let uu____13875 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13875
                                                    in
                                                 (uu____13874,
                                                   (Some "kinding"),
                                                   (Some
                                                      (Prims.strcat
                                                         "pre_kinding_" ttok)))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____13869
                                                in
                                             [uu____13868]
                                           else []  in
                                         let uu____13879 =
                                           let uu____13881 =
                                             let uu____13883 =
                                               let uu____13884 =
                                                 let uu____13889 =
                                                   let uu____13890 =
                                                     let uu____13896 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____13896)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13890
                                                    in
                                                 (uu____13889, None,
                                                   (Some
                                                      (Prims.strcat
                                                         "kinding_" ttok)))
                                                  in
                                               FStar_SMTEncoding_Term.Assume
                                                 uu____13884
                                                in
                                             [uu____13883]  in
                                           FStar_List.append karr uu____13881
                                            in
                                         FStar_List.append decls1 uu____13879
                                      in
                                   let aux =
                                     let uu____13906 =
                                       let uu____13908 =
                                         inversion_axioms tapp vars  in
                                       let uu____13910 =
                                         let uu____13912 =
                                           pretype_axiom tapp vars  in
                                         [uu____13912]  in
                                       FStar_List.append uu____13908
                                         uu____13910
                                        in
                                     FStar_List.append kindingAx uu____13906
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13917,uu____13918,uu____13919,uu____13920,uu____13921,uu____13922,uu____13923)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13930,t,uu____13932,n_tps,quals,uu____13935,drange) ->
          let uu____13941 = new_term_constant_and_tok_from_lid env d  in
          (match uu____13941 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____13952 =
                 FStar_TypeChecker_Util.arrow_formals env1.tcenv t  in
               (match uu____13952 with
                | (formals,t_res) ->
                    let uu____13959 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____13959 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____13968 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____13968 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14006 =
                                            mk_term_projector_name d x  in
                                          (uu____14006,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14008 =
                                  let uu____14018 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14018, true)
                                   in
                                FStar_All.pipe_right uu____14008
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
                              let uu____14040 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14040 with
                               | (tok_typing,decls3) ->
                                   let uu____14047 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14047 with
                                    | (vars',guards',env'',decls_formals,uu____14062)
                                        ->
                                        let uu____14069 =
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
                                        (match uu____14069 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14088 ->
                                                   let uu____14089 =
                                                     let uu____14090 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14090
                                                      in
                                                   [uu____14089]
                                                in
                                             let encode_elim uu____14097 =
                                               let uu____14098 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14098 with
                                               | (head1,args) ->
                                                   let uu____14127 =
                                                     let uu____14128 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14128.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14127 with
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
                                                        let uu____14146 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14146
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
                                                                 | uu____14172
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
                                                                    let uu____14180
                                                                    =
                                                                    let uu____14181
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14181
                                                                     in
                                                                    if
                                                                    uu____14180
                                                                    then
                                                                    let uu____14188
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14188]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14190
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14203
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14203
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14225
                                                                    =
                                                                    let uu____14229
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14229
                                                                     in
                                                                    (match uu____14225
                                                                    with
                                                                    | 
                                                                    (uu____14236,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14242
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14242
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14244
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14244
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
                                                             (match uu____14190
                                                              with
                                                              | (uu____14252,arg_vars,elim_eqns_or_guards,uu____14255)
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
                                                                    let uu____14274
                                                                    =
                                                                    let uu____14279
                                                                    =
                                                                    let uu____14280
                                                                    =
                                                                    let uu____14286
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14292
                                                                    =
                                                                    let uu____14293
                                                                    =
                                                                    let uu____14296
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14296)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14293
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14286,
                                                                    uu____14292)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14280
                                                                     in
                                                                    (uu____14279,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14274
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14310
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14310,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14312
                                                                    =
                                                                    let uu____14317
                                                                    =
                                                                    let uu____14318
                                                                    =
                                                                    let uu____14324
                                                                    =
                                                                    let uu____14327
                                                                    =
                                                                    let uu____14329
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14329]
                                                                     in
                                                                    [uu____14327]
                                                                     in
                                                                    let uu____14332
                                                                    =
                                                                    let uu____14333
                                                                    =
                                                                    let uu____14336
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14337
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14336,
                                                                    uu____14337)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14333
                                                                     in
                                                                    (uu____14324,
                                                                    [x],
                                                                    uu____14332)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14318
                                                                     in
                                                                    let uu____14347
                                                                    =
                                                                    let uu____14349
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    Some
                                                                    uu____14349
                                                                     in
                                                                    (uu____14317,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14347)
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14312
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14355
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
                                                                    (let uu____14370
                                                                    =
                                                                    let uu____14371
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14371
                                                                    dapp1  in
                                                                    [uu____14370])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14355
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14375
                                                                    =
                                                                    let uu____14380
                                                                    =
                                                                    let uu____14381
                                                                    =
                                                                    let uu____14387
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14393
                                                                    =
                                                                    let uu____14394
                                                                    =
                                                                    let uu____14397
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14397)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14394
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14387,
                                                                    uu____14393)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14381
                                                                     in
                                                                    (uu____14380,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14375)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14408 ->
                                                        ((let uu____14410 =
                                                            let uu____14411 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____14412 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14411
                                                              uu____14412
                                                             in
                                                          FStar_Errors.warn
                                                            drange
                                                            uu____14410);
                                                         ([], [])))
                                                in
                                             let uu____14415 = encode_elim ()
                                                in
                                             (match uu____14415 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14427 =
                                                      let uu____14429 =
                                                        let uu____14431 =
                                                          let uu____14433 =
                                                            let uu____14435 =
                                                              let uu____14436
                                                                =
                                                                let uu____14442
                                                                  =
                                                                  let uu____14444
                                                                    =
                                                                    let uu____14445
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14445
                                                                     in
                                                                  Some
                                                                    uu____14444
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14442)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14436
                                                               in
                                                            [uu____14435]  in
                                                          let uu____14448 =
                                                            let uu____14450 =
                                                              let uu____14452
                                                                =
                                                                let uu____14454
                                                                  =
                                                                  let uu____14456
                                                                    =
                                                                    let uu____14458
                                                                    =
                                                                    let uu____14460
                                                                    =
                                                                    let uu____14461
                                                                    =
                                                                    let uu____14466
                                                                    =
                                                                    let uu____14467
                                                                    =
                                                                    let uu____14473
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14473)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14467
                                                                     in
                                                                    (uu____14466,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14461
                                                                     in
                                                                    let uu____14481
                                                                    =
                                                                    let uu____14483
                                                                    =
                                                                    let uu____14484
                                                                    =
                                                                    let uu____14489
                                                                    =
                                                                    let uu____14490
                                                                    =
                                                                    let uu____14496
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____14502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14496,
                                                                    uu____14502)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14490
                                                                     in
                                                                    (uu____14489,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14484
                                                                     in
                                                                    [uu____14483]
                                                                     in
                                                                    uu____14460
                                                                    ::
                                                                    uu____14481
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
                                                                    uu____14458
                                                                     in
                                                                  FStar_List.append
                                                                    uu____14456
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14454
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14452
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14450
                                                             in
                                                          FStar_List.append
                                                            uu____14433
                                                            uu____14448
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____14431
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____14429
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14427
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
           (fun uu____14525  ->
              fun se  ->
                match uu____14525 with
                | (g,env1) ->
                    let uu____14537 = encode_sigelt env1 se  in
                    (match uu____14537 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14573 =
        match uu____14573 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14591 ->
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
                 ((let uu____14596 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____14596
                   then
                     let uu____14597 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____14598 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____14599 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14597 uu____14598 uu____14599
                   else ());
                  (let uu____14601 = encode_term t1 env1  in
                   match uu____14601 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____14611 =
                         let uu____14615 =
                           let uu____14616 =
                             let uu____14617 =
                               FStar_Util.digest_of_string t_hash  in
                             let uu____14618 =
                               let uu____14619 = FStar_Util.string_of_int i
                                  in
                               Prims.strcat "_" uu____14619  in
                             Prims.strcat uu____14617 uu____14618  in
                           Prims.strcat "x_" uu____14616  in
                         new_term_constant_from_string env1 x uu____14615  in
                       (match uu____14611 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____14630 = FStar_Options.log_queries ()
                                 in
                              if uu____14630
                              then
                                let uu____14632 =
                                  let uu____14633 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____14634 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____14635 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14633 uu____14634 uu____14635
                                   in
                                Some uu____14632
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14648,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____14657 = encode_free_var env1 fv t t_norm []  in
                 (match uu____14657 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14676 = encode_sigelt env1 se  in
                 (match uu____14676 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____14686 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____14686 with | (uu____14698,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14743  ->
            match uu____14743 with
            | (l,uu____14750,uu____14751) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14772  ->
            match uu____14772 with
            | (l,uu____14780,uu____14781) ->
                let uu____14786 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l)
                   in
                let uu____14787 =
                  let uu____14789 =
                    let uu____14790 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____14790  in
                  [uu____14789]  in
                uu____14786 :: uu____14787))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14801 =
      let uu____14803 =
        let uu____14804 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14804;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [uu____14803]  in
    FStar_ST.write last_env uu____14801
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____14822 = FStar_ST.read last_env  in
    match uu____14822 with
    | [] -> failwith "No env; call init first!"
    | e::uu____14828 ->
        let uu___158_14830 = e  in
        {
          bindings = (uu___158_14830.bindings);
          depth = (uu___158_14830.depth);
          tcenv;
          warn = (uu___158_14830.warn);
          cache = (uu___158_14830.cache);
          nolabels = (uu___158_14830.nolabels);
          use_zfuel_name = (uu___158_14830.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___158_14830.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____14834 = FStar_ST.read last_env  in
    match uu____14834 with
    | [] -> failwith "Empty env stack"
    | uu____14839::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____14847  ->
    let uu____14848 = FStar_ST.read last_env  in
    match uu____14848 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___159_14869 = hd1  in
          {
            bindings = (uu___159_14869.bindings);
            depth = (uu___159_14869.depth);
            tcenv = (uu___159_14869.tcenv);
            warn = (uu___159_14869.warn);
            cache = refs;
            nolabels = (uu___159_14869.nolabels);
            use_zfuel_name = (uu___159_14869.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___159_14869.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____14875  ->
    let uu____14876 = FStar_ST.read last_env  in
    match uu____14876 with
    | [] -> failwith "Popping an empty stack"
    | uu____14881::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____14889  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____14892  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____14895  ->
    let uu____14896 = FStar_ST.read last_env  in
    match uu____14896 with
    | hd1::uu____14902::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____14908 -> failwith "Impossible"
  
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
        let uu____14953 = FStar_Options.log_queries ()  in
        if uu____14953
        then
          let uu____14955 =
            let uu____14956 =
              let uu____14957 =
                let uu____14958 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____14958 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____14957  in
            FStar_SMTEncoding_Term.Caption uu____14956  in
          uu____14955 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____14965 = encode_sigelt env se  in
      match uu____14965 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____14971 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____14971))
  
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
      (let uu____14982 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____14982
       then
         let uu____14983 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             FStar_Util.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____14983
       else ());
      (let env = get_env tcenv  in
       let uu____14988 =
         encode_signature
           (let uu___160_14992 = env  in
            {
              bindings = (uu___160_14992.bindings);
              depth = (uu___160_14992.depth);
              tcenv = (uu___160_14992.tcenv);
              warn = false;
              cache = (uu___160_14992.cache);
              nolabels = (uu___160_14992.nolabels);
              use_zfuel_name = (uu___160_14992.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_14992.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____14988 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15004 = FStar_Options.log_queries ()  in
             if uu____15004
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___161_15009 = env1  in
               {
                 bindings = (uu___161_15009.bindings);
                 depth = (uu___161_15009.depth);
                 tcenv = (uu___161_15009.tcenv);
                 warn = true;
                 cache = (uu___161_15009.cache);
                 nolabels = (uu___161_15009.nolabels);
                 use_zfuel_name = (uu___161_15009.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_15009.encode_non_total_function_typ)
               });
            (let uu____15011 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15011
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
        (let uu____15046 =
           let uu____15047 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____15047.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15046);
        (let env = get_env tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____15055 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15076 = aux rest  in
                 (match uu____15076 with
                  | (out,rest1) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort
                         in
                      let uu____15092 =
                        let uu____15094 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_15095 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_15095.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_15095.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             })
                           in
                        uu____15094 :: out  in
                      (uu____15092, rest1))
             | uu____15098 -> ([], bindings1)  in
           let uu____15102 = aux bindings  in
           match uu____15102 with
           | (closing,bindings1) ->
               let uu____15116 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q
                  in
               (uu____15116, bindings1)
            in
         match uu____15055 with
         | (q1,bindings1) ->
             let uu____15129 =
               let uu____15132 =
                 FStar_List.filter
                   (fun uu___134_15134  ->
                      match uu___134_15134 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15135 ->
                          false
                      | uu____15139 -> true) bindings1
                  in
               encode_env_bindings env uu____15132  in
             (match uu____15129 with
              | (env_decls,env1) ->
                  ((let uu____15150 =
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
                    if uu____15150
                    then
                      let uu____15151 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15151
                    else ());
                   (let uu____15153 = encode_formula q1 env1  in
                    match uu____15153 with
                    | (phi,qdecls) ->
                        let uu____15165 =
                          let uu____15168 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15168 phi
                           in
                        (match uu____15165 with
                         | (labels,phi1) ->
                             let uu____15178 = encode_labels labels  in
                             (match uu____15178 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____15199 =
                                      let uu____15204 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____15205 =
                                        let uu____15207 =
                                          varops.mk_unique "@query"  in
                                        Some uu____15207  in
                                      (uu____15204, (Some "query"),
                                        uu____15205)
                                       in
                                    FStar_SMTEncoding_Term.Assume uu____15199
                                     in
                                  let suffix =
                                    let uu____15212 =
                                      let uu____15214 =
                                        let uu____15216 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____15216
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append uu____15214
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix
                                      uu____15212
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15229 = encode_formula q env  in
       match uu____15229 with
       | (f,uu____15233) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15235) -> true
             | uu____15238 -> false)))
  