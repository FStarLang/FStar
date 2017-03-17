open Prims
let add_fuel x tl =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
  match uu____16 with | true  -> tl | uu____18 -> x :: tl 
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c) 
let vargs args =
  FStar_List.filter
    (fun uu___111_74  ->
       match uu___111_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
  
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l) ->
      Some
        (FStar_Util.Inl
           (let _0_266 =
              let _0_265 = l.FStar_Syntax_Syntax.comp ()  in
              FStar_Syntax_Subst.subst_comp s _0_265  in
            FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_266))
  | uu____118 -> l 
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a =
        let uu___134_132 = a  in
        let _0_267 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___134_132.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___134_132.FStar_Syntax_Syntax.sort)
        }  in
      let _0_268 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape _0_268
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____145 =
          failwith
            (let _0_269 = FStar_Util.string_of_int i  in
             FStar_Util.format2
               "Projector %s on data constructor %s not found" _0_269
               lid.FStar_Ident.str)
           in
        let uu____146 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____146 with
        | (uu____149,t) ->
            let uu____151 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            (match uu____151 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____164 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____164 with
                  | (binders,uu____168) ->
                      (match (i < (Prims.parse_int "0")) ||
                               (i >= (FStar_List.length binders))
                       with
                       | true  -> fail ()
                       | uu____173 ->
                           let b = FStar_List.nth binders i  in
                           mk_term_projector_name lid (Prims.fst b)))
             | uu____179 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let _0_271 =
        let _0_270 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _0_270  in
      FStar_All.pipe_left escape _0_271
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_272 = mk_term_projector_name lid a  in
         (_0_272,
           (FStar_SMTEncoding_Term.Arrow
              (FStar_SMTEncoding_Term.Term_sort,
                FStar_SMTEncoding_Term.Term_sort))))
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_273 = mk_term_projector_name_by_pos lid i  in
         (_0_273,
           (FStar_SMTEncoding_Term.Arrow
              (FStar_SMTEncoding_Term.Term_sort,
                FStar_SMTEncoding_Term.Term_sort))))
  
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
  let new_scope uu____387 =
    let _0_275 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let _0_274 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (_0_275, _0_274)  in
  let scopes = FStar_Util.mk_ref (let _0_276 = new_scope ()  in [_0_276])  in
  let mk_unique y =
    let y = escape y  in
    let y =
      let uu____417 =
        let _0_277 = FStar_ST.read scopes  in
        FStar_Util.find_map _0_277
          (fun uu____430  ->
             match uu____430 with
             | (names,uu____437) -> FStar_Util.smap_try_find names y)
         in
      match uu____417 with
      | None  -> y
      | Some uu____442 ->
          (FStar_Util.incr ctr;
           (let _0_279 =
              let _0_278 = FStar_Util.string_of_int (FStar_ST.read ctr)  in
              Prims.strcat "__" _0_278  in
            Prims.strcat y _0_279))
       in
    let top_scope =
      let _0_280 = FStar_List.hd (FStar_ST.read scopes)  in
      FStar_All.pipe_left Prims.fst _0_280  in
    FStar_Util.smap_add top_scope y true; y  in
  let new_var pp rn =
    let _0_283 =
      let _0_282 =
        let _0_281 = FStar_Util.string_of_int rn  in Prims.strcat "__" _0_281
         in
      Prims.strcat pp.FStar_Ident.idText _0_282  in
    FStar_All.pipe_left mk_unique _0_283  in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id uu____484 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh pfx =
    let _0_285 =
      let _0_284 = next_id ()  in
      FStar_All.pipe_left FStar_Util.string_of_int _0_284  in
    FStar_Util.format2 "%s_%s" pfx _0_285  in
  let string_const s =
    let uu____499 =
      let _0_286 = FStar_ST.read scopes  in
      FStar_Util.find_map _0_286
        (fun uu____512  ->
           match uu____512 with
           | (uu____518,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____499 with
    | Some f -> f
    | None  ->
        let id = next_id ()  in
        let f =
          let _0_287 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _0_287  in
        let top_scope =
          let _0_288 = FStar_List.hd (FStar_ST.read scopes)  in
          FStar_All.pipe_left Prims.snd _0_288  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push uu____551 =
    let _0_291 =
      let _0_290 = new_scope ()  in
      let _0_289 = FStar_ST.read scopes  in _0_290 :: _0_289  in
    FStar_ST.write scopes _0_291  in
  let pop uu____573 =
    let _0_292 = FStar_List.tl (FStar_ST.read scopes)  in
    FStar_ST.write scopes _0_292  in
  let mark uu____595 = push ()  in
  let reset_mark uu____599 = pop ()  in
  let commit_mark uu____603 =
    let uu____604 = FStar_ST.read scopes  in
    match uu____604 with
    | (hd1,hd2)::(next1,next2)::tl ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next2 key value) ();
         FStar_ST.write scopes ((next1, next2) :: tl))
    | uu____664 -> failwith "Impossible"  in
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
    let uu___135_673 = x  in
    let _0_293 =
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
    match projectee with | Binding_var _0 -> true | uu____694 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____718 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term
      Prims.option * FStar_SMTEncoding_Term.term Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar v = (v, None) 
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
    let uu____952 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___112_956  ->
              match uu___112_956 with
              | Binding_var (x,uu____958) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____844,uu____845,uu____846) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right _0_294 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____878 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      match uu____878 with
      | true  -> Some (FStar_Syntax_Print.term_to_string t)
      | uu____880 -> None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let _0_295 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, _0_295)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        let _0_296 = FStar_Util.string_of_int env.depth  in
        Prims.strcat "@x" _0_296  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___136_901 = env  in
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
        (let uu___137_914 = env  in
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
          (let uu___138_930 = env  in
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
        let uu___139_940 = env  in
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
             | uu____964 -> None)
         in
      let uu____967 = aux a  in
      match uu____967 with
      | None  ->
          let a = unmangle a  in
          let uu____974 = aux a  in
          (match uu____974 with
           | None  ->
               failwith
                 (let _0_297 = FStar_Syntax_Print.bv_to_string a  in
                  FStar_Util.format1
                    "Bound term variable not found (after unmangling): %s"
                    _0_297)
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let _0_303 =
        let uu___140_999 = env  in
        let _0_302 =
          let _0_301 =
            Binding_fvar
              (let _0_300 =
                 let _0_299 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                 FStar_All.pipe_left (fun _0_298  -> Some _0_298) _0_299  in
               (x, fname, _0_300, None))
             in
          _0_301 :: (env.bindings)  in
        {
          bindings = uu____1123;
          depth = (uu___141_1122.depth);
          tcenv = (uu___141_1122.tcenv);
          warn = (uu___141_1122.warn);
          cache = (uu___141_1122.cache);
          nolabels = (uu___141_1122.nolabels);
          use_zfuel_name = (uu___141_1122.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_999.encode_non_total_function_typ)
        }  in
      (fname, ftok, _0_303)
  
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
           | uu____1043 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1191 =
        lookup_binding env
          (fun uu___115_1193  ->
             match uu___115_1193 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1066 -> None)
         in
      FStar_All.pipe_right _0_304 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1078 = try_lookup_lid env a  in
      match uu____1078 with
      | None  ->
          failwith
            (let _0_305 = FStar_Syntax_Print.lid_to_string a  in
             FStar_Util.format1 "Name not found: %s" _0_305)
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
          let uu___141_1125 = env  in
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
        let uu____1137 = lookup_lid env x  in
        match uu____1137 with
        | (t1,t2,uu____1145) ->
            let t3 =
              FStar_SMTEncoding_Util.mkApp
                (let _0_307 =
                   let _0_306 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                      in
                   [_0_306]  in
                 (f, _0_307))
               in
            let uu___142_1153 = env  in
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
      let uu____1163 = try_lookup_lid env l  in
      match uu____1163 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1337 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1195,fuel::[]) ->
                         let uu____1198 =
                           let _0_309 =
                             let _0_308 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right _0_308 Prims.fst  in
                           FStar_Util.starts_with _0_309 "fuel"  in
                         (match uu____1198 with
                          | true  ->
                              let _0_312 =
                                let _0_311 =
                                  FStar_SMTEncoding_Util.mkFreeV
                                    (name, FStar_SMTEncoding_Term.Term_sort)
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF _0_311 fuel
                                 in
                              FStar_All.pipe_left
                                (fun _0_310  -> Some _0_310) _0_312
                          | uu____1201 -> Some t)
                     | uu____1202 -> Some t)
                | uu____1203 -> None))
  
let lookup_free_var env a =
  let uu____1221 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1221 with
  | Some t -> t
  | None  ->
      failwith
        (let _0_313 =
           FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
         FStar_Util.format1 "Name not found: %s" _0_313)
  
let lookup_free_var_name env a =
  let uu____1240 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1240 with | (x,uu____1247,uu____1248) -> x 
let lookup_free_var_sym env a =
  let uu____1272 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1272 with
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
                 | uu____1316 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___116_1478  ->
           match uu___116_1478 with
           | Binding_fvar (uu____1480,nm',tok,uu____1483) when nm = nm' ->
               tok
           | uu____1335 -> None)
  
let mkForall_fuel' n uu____1352 =
  match uu____1352 with
  | (pats,vars,body) ->
      let fallback uu____1368 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1371 = FStar_Options.unthrottle_inductives ()  in
      (match uu____1371 with
       | true  -> fallback ()
       | uu____1372 ->
           let uu____1373 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
              in
           (match uu____1373 with
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
                          | uu____1392 -> p))
                   in
                let pats = FStar_List.map add_fuel pats  in
                let body =
                  match body.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                      let guard =
                        match guard.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App
                            (FStar_SMTEncoding_Term.And ,guards) ->
                            FStar_SMTEncoding_Util.mk_and_l (add_fuel guards)
                        | uu____1406 ->
                            let _0_314 = add_fuel [guard]  in
                            FStar_All.pipe_right _0_314 FStar_List.hd
                         in
                      FStar_SMTEncoding_Util.mkImp (guard, body')
                  | uu____1408 -> body  in
                let vars = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                   in
                FStar_SMTEncoding_Util.mkForall (pats, vars, body)))
  
let mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
    FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1") 
let head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t  in
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
          let uu____1609 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_315 FStar_Option.isNone
      | uu____1461 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1468 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____1468 with
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
          FStar_All.pipe_right _0_316 FStar_Option.isSome
      | uu____1538 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1545 = head_normal env t  in
      match uu____1545 with
      | true  -> t
      | uu____1546 ->
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
    let _0_319 = let _0_317 = FStar_Syntax_Syntax.null_binder t  in [_0_317]
       in
    let _0_318 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs _0_319 _0_318 None
  
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
                    let _0_320 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out _0_320
                | s ->
                    let _0_321 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out _0_321) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_1595  ->
    match uu___116_1595 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1596 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1800;
                       FStar_SMTEncoding_Term.rng = uu____1801;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1815) ->
              let uu____1820 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1654 -> false) args vars)
                 in
              (match uu____1644 with
               | true  -> tok_of_name env f
               | uu____1656 -> None)
          | (uu____1657,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1660 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        Prims.op_Negation
                          (FStar_Util.for_some
                             (FStar_SMTEncoding_Term.fv_eq fv) vars)))
                 in
              (match uu____1660 with | true  -> Some t | uu____1663 -> None)
          | uu____1664 -> None  in
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
    | uu____1748 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_1751  ->
    match uu___117_1751 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        FStar_SMTEncoding_Util.mkApp
          (let _0_323 =
             let _0_322 =
               FStar_SMTEncoding_Term.boxInt
                 (FStar_SMTEncoding_Util.mkInteger'
                    (FStar_Util.int_of_char c))
                in
             [_0_322]  in
           ("FStar.Char.Char", _0_323))
    | FStar_Const.Const_int (i,None ) ->
        let uu____1960 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____1960
    | FStar_Const.Const_int (i,Some uu____1962) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1971) ->
        let uu____1974 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____1974
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        failwith
          (let _0_324 = FStar_Syntax_Print.const_to_string c  in
           FStar_Util.format1 "Unhandled constant: %s" _0_324)
  
let as_function_typ :
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm t =
        let t = FStar_Syntax_Subst.compress t  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____1794 -> t
        | FStar_Syntax_Syntax.Tm_refine uu____1802 ->
            let _0_325 = FStar_Syntax_Util.unrefine t  in aux true _0_325
        | uu____1807 ->
            (match norm with
             | true  -> let _0_326 = whnf env t  in aux false _0_326
             | uu____1808 ->
                 failwith
                   (let _0_328 =
                      FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos
                       in
                    let _0_327 = FStar_Syntax_Print.term_to_string t0  in
                    FStar_Util.format2 "(%s) Expected a function typ; got %s"
                      _0_328 _0_327))
         in
      aux true t0
  
let curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k = FStar_Syntax_Subst.compress k  in
    match k.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____1829 ->
        let _0_329 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_329)
  
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
        (let uu____1972 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         match uu____1972 with
         | true  ->
             let _0_330 = FStar_Syntax_Print.binders_to_string ", " bs  in
             FStar_Util.print1 "Encoding binders %s\n" _0_330
         | uu____1973 -> ());
        (let uu____1974 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2221  ->
                   fun b  ->
                     match uu____2010 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2053 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2062 = gen_term_var env x  in
                           match uu____2062 with
                           | (xxsym,xx,env') ->
                               let uu____2076 =
                                 let _0_331 =
                                   norm env x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt _0_331 env xx  in
                               (match uu____2076 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2053 with
                          | (v,g,env,decls',n) ->
                              ((v :: vars), (g :: guards), env,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], []))
            in
         match uu____1974 with
         | (vars,guards,env,decls,names) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env, decls,
               (FStar_List.rev names)))

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
          let uu____2166 = encode_term t env  in
          match uu____2166 with
          | (t,decls) ->
              let _0_332 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t  in
              (_0_332, decls)

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
          let uu____2180 = encode_term t env  in
          match uu____2180 with
          | (t,decls) ->
              (match fuel_opt with
               | None  ->
                   let _0_333 = FStar_SMTEncoding_Term.mk_HasTypeZ e t  in
                   (_0_333, decls)
               | Some f ->
                   let _0_334 = FStar_SMTEncoding_Term.mk_HasTypeFuel f e t
                      in
                   (_0_334, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2196 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       match uu____2196 with
       | true  ->
           let _0_337 = FStar_Syntax_Print.tag_of_term t  in
           let _0_336 = FStar_Syntax_Print.tag_of_term t0  in
           let _0_335 = FStar_Syntax_Print.term_to_string t0  in
           FStar_Util.print3 "(%s) (%s)   %s\n" _0_337 _0_336 _0_335
       | uu____2197 -> ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           failwith
             (let _0_341 =
                FStar_All.pipe_left FStar_Range.string_of_range
                  t.FStar_Syntax_Syntax.pos
                 in
              let _0_340 = FStar_Syntax_Print.tag_of_term t0  in
              let _0_339 = FStar_Syntax_Print.term_to_string t0  in
              let _0_338 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_341
                _0_340 _0_339 _0_338)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           failwith
             (let _0_342 = FStar_Syntax_Print.bv_to_string x  in
              FStar_Util.format1 "Impossible: locally nameless; got %s"
                _0_342)
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2208) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2228) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x  in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let _0_343 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name  in
           (_0_343, [])
       | FStar_Syntax_Syntax.Tm_type uu____2242 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2481) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let _0_344 = encode_const c  in (_0_344, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2264 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2264 with
            | (binders,res) ->
                let uu____2271 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                (match uu____2271 with
                 | true  ->
                     let uu____2274 = encode_binders None binders env  in
                     (match uu____2274 with
                      | (vars,guards,env',decls,uu____2289) ->
                          let fsym =
                            let _0_345 = varops.fresh "f"  in
                            (_0_345, FStar_SMTEncoding_Term.Term_sort)  in
                          let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                          let app = mk_Apply f vars  in
                          let uu____2301 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              (let uu___143_2305 = env.tcenv  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___143_2305.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___143_2305.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___143_2305.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___143_2305.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___143_2305.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___143_2305.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___143_2305.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___143_2305.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___143_2305.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___143_2305.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___143_2305.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___143_2305.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___143_2305.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___143_2305.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___143_2305.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___143_2305.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___143_2305.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___143_2305.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___143_2305.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___143_2305.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___143_2305.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___143_2305.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___143_2305.FStar_TypeChecker_Env.qname_and_index)
                               }) res
                             in
                          (match uu____2301 with
                           | (pre_opt,res_t) ->
                               let uu____2312 =
                                 encode_term_pred None res_t env' app  in
                               (match uu____2312 with
                                | (res_pred,decls') ->
                                    let uu____2319 =
                                      match pre_opt with
                                      | None  ->
                                          let _0_346 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards
                                             in
                                          (_0_346, [])
                                      | Some pre ->
                                          let uu____2328 =
                                            encode_formula pre env'  in
                                          (match uu____2328 with
                                           | (guard,decls0) ->
                                               let _0_347 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (guard :: guards)
                                                  in
                                               (_0_347, decls0))
                                       in
                                    (match uu____2319 with
                                     | (guards,guard_decls) ->
                                         let t_interp =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_348 =
                                                FStar_SMTEncoding_Util.mkImp
                                                  (guards, res_pred)
                                                 in
                                              ([[app]], vars, _0_348))
                                            in
                                         let cvars =
                                           let _0_349 =
                                             FStar_SMTEncoding_Term.free_variables
                                               t_interp
                                              in
                                           FStar_All.pipe_right _0_349
                                             (FStar_List.filter
                                                (fun uu____2357  ->
                                                   match uu____2357 with
                                                   | (x,uu____2361) ->
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
                                         let uu____2372 =
                                           FStar_Util.smap_try_find env.cache
                                             tkey_hash
                                            in
                                         (match uu____2372 with
                                          | Some (t',sorts,uu____2388) ->
                                              let _0_351 =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (let _0_350 =
                                                     FStar_All.pipe_right
                                                       cvars
                                                       (FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV)
                                                      in
                                                   (t', _0_350))
                                                 in
                                              (_0_351, [])
                                          | None  ->
                                              let tsym =
                                                varops.mk_unique
                                                  (let _0_352 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.strcat "Tm_arrow_"
                                                     _0_352)
                                                 in
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars
                                                 in
                                              let caption =
                                                let uu____2418 =
                                                  FStar_Options.log_queries
                                                    ()
                                                   in
                                                match uu____2418 with
                                                | true  ->
                                                    Some
                                                      (FStar_TypeChecker_Normalize.term_to_string
                                                         env.tcenv t0)
                                                | uu____2420 -> None  in
                                              let tdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (tsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    caption)
                                                 in
                                              let t =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (let _0_353 =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       cvars
                                                      in
                                                   (tsym, _0_353))
                                                 in
                                              let t_has_kind =
                                                FStar_SMTEncoding_Term.mk_HasType
                                                  t
                                                  FStar_SMTEncoding_Term.mk_Term_type
                                                 in
                                              let k_assumption =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat "kinding_"
                                                       tsym)
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_354 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[t_has_kind]],
                                                         cvars, t_has_kind)
                                                      in
                                                   (_0_354, a_name, a_name))
                                                 in
                                              let f_has_t =
                                                FStar_SMTEncoding_Term.mk_HasType
                                                  f t
                                                 in
                                              let f_has_t_z =
                                                FStar_SMTEncoding_Term.mk_HasTypeZ
                                                  f t
                                                 in
                                              let pre_typing =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "pre_typing_" tsym)
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_358 =
                                                     mkForall_fuel
                                                       (let _0_357 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (let _0_356 =
                                                               let _0_355 =
                                                                 FStar_SMTEncoding_Term.mk_PreType
                                                                   f
                                                                  in
                                                               FStar_SMTEncoding_Term.mk_tester
                                                                 "Tm_arrow"
                                                                 _0_355
                                                                in
                                                             (f_has_t,
                                                               _0_356))
                                                           in
                                                        ([[f_has_t]], (fsym
                                                          :: cvars), _0_357))
                                                      in
                                                   (_0_358,
                                                     (Some
                                                        "pre-typing for functions"),
                                                     a_name))
                                                 in
                                              let t_interp =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" tsym)
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_360 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_359 =
                                                          FStar_SMTEncoding_Util.mkIff
                                                            (f_has_t_z,
                                                              t_interp)
                                                           in
                                                        ([[f_has_t_z]], (fsym
                                                          :: cvars), _0_359))
                                                      in
                                                   (_0_360, a_name, a_name))
                                                 in
                                              let t_decls =
                                                FStar_List.append (tdecl ::
                                                  decls)
                                                  (FStar_List.append decls'
                                                     (FStar_List.append
                                                        guard_decls
                                                        [k_assumption;
                                                        pre_typing;
                                                        t_interp]))
                                                 in
                                              (FStar_Util.smap_add env.cache
                                                 tkey_hash
                                                 (tsym, cvar_sorts, t_decls);
                                               (t, t_decls)))))))
                 | uu____2482 ->
                     let tsym = varops.fresh "Non_total_Tm_arrow"  in
                     let tdecl =
                       FStar_SMTEncoding_Term.DeclFun
                         (tsym, [], FStar_SMTEncoding_Term.Term_sort, None)
                        in
                     let t = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                     let t_kinding =
                       let a_name =
                         Some
                           (Prims.strcat "non_total_function_typing_" tsym)
                          in
                       FStar_SMTEncoding_Term.Assume
                         (let _0_361 =
                            FStar_SMTEncoding_Term.mk_HasType t
                              FStar_SMTEncoding_Term.mk_Term_type
                             in
                          (_0_361, (Some "Typing for non-total arrows"),
                            a_name))
                        in
                     let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                     let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                     let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t  in
                     let t_interp =
                       let a_name = Some (Prims.strcat "pre_typing_" tsym)
                          in
                       FStar_SMTEncoding_Term.Assume
                         (let _0_365 =
                            mkForall_fuel
                              (let _0_364 =
                                 FStar_SMTEncoding_Util.mkImp
                                   (let _0_363 =
                                      let _0_362 =
                                        FStar_SMTEncoding_Term.mk_PreType f
                                         in
                                      FStar_SMTEncoding_Term.mk_tester
                                        "Tm_arrow" _0_362
                                       in
                                    (f_has_t, _0_363))
                                  in
                               ([[f_has_t]], [fsym], _0_364))
                             in
                          (_0_365, a_name, a_name))
                        in
                     (t, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2516 ->
           let uu____2521 =
             let uu____2524 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2524 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2529;
                 FStar_Syntax_Syntax.pos = uu____2530;
                 FStar_Syntax_Syntax.vars = uu____2531;_} ->
                 let uu____2538 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2538 with
                  | (b,f) ->
                      let _0_366 = Prims.fst (FStar_List.hd b)  in
                      (_0_366, f))
             | uu____2554 -> failwith "impossible"  in
           (match uu____2521 with
            | (x,f) ->
                let uu____2561 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2561 with
                 | (base_t,decls) ->
                     let uu____2568 = gen_term_var env x  in
                     (match uu____2568 with
                      | (x,xtm,env') ->
                          let uu____2577 = encode_formula f env'  in
                          (match uu____2577 with
                           | (refinement,decls') ->
                               let uu____2899 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2584 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (let _0_367 =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm base_t
                                            in
                                         (_0_367, refinement))
                                       in
                                    let cvars =
                                      let _0_368 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right _0_368
                                        (FStar_List.filter
                                           (fun uu____2601  ->
                                              match uu____2601 with
                                              | (y,uu____2605) ->
                                                  (y <> x) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x, FStar_SMTEncoding_Term.Term_sort)
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
                                    let uu____2624 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2624 with
                                     | Some (t,uu____2639,uu____2640) ->
                                         let _0_370 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_369 =
                                                FStar_All.pipe_right cvars
                                                  (FStar_List.map
                                                     FStar_SMTEncoding_Util.mkFreeV)
                                                 in
                                              (t, _0_369))
                                            in
                                         (_0_370, [])
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           varops.mk_unique
                                             (let _0_371 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "Tm_refine_"
                                                _0_371)
                                            in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars  in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_372 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (tsym, _0_372))
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t
                                            in
                                         let t_haseq =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_374 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_373 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (t_haseq_ref,
                                                         t_haseq_base)
                                                      in
                                                   ([[t_haseq_ref]], cvars,
                                                     _0_373))
                                                 in
                                              (_0_374,
                                                (Some
                                                   (Prims.strcat "haseq for "
                                                      tsym)),
                                                (Some
                                                   (Prims.strcat "haseq" tsym))))
                                            in
                                         let t_kinding =
                                           let uu____3049 =
                                             let uu____3053 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3053,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_375 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  ([[t_has_kind]], cvars,
                                                    t_has_kind)
                                                 in
                                              (_0_375,
                                                (Some "refinement kinding"),
                                                (Some
                                                   (Prims.strcat
                                                      "refinement_kinding_"
                                                      tsym))))
                                            in
                                         let t_interp =
                                           let uu____3063 =
                                             let uu____3067 =
                                               let uu____3068 =
                                                 let uu____3074 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3074) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3068 in
                                             let uu____3086 =
                                               let uu____3088 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3088 in
                                             (uu____3067, uu____3086,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_378 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_376 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (x_has_t, encoding)
                                                      in
                                                   ([[x_has_t]], (ffv :: xfv
                                                     :: cvars), _0_376))
                                                 in
                                              let _0_377 =
                                                Some
                                                  (FStar_Syntax_Print.term_to_string
                                                     t0)
                                                 in
                                              (_0_378, _0_377,
                                                (Some
                                                   (Prims.strcat
                                                      "refinement_interpretation_"
                                                      tsym))))
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq])
                                            in
                                         (FStar_Util.smap_add env.cache
                                            tkey_hash
                                            (tsym, cvar_sorts, t_decls);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             FStar_SMTEncoding_Util.mk_Term_uvar (FStar_Unionfind.uvar_id uv)
              in
           let uu____2742 = encode_term_pred None k env ttm  in
           (match uu____2742 with
            | (t_has_k,decls) ->
                let d =
                  FStar_SMTEncoding_Term.Assume
                    (let _0_381 =
                       Some
                         (varops.mk_unique
                            (let _0_380 =
                               let _0_379 = FStar_Unionfind.uvar_id uv  in
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 _0_379
                                in
                             FStar_Util.format1 "uvar_typing_%s" _0_380))
                        in
                     (t_has_k, (Some "Uvar typing"), _0_381))
                   in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____2756 ->
           let uu____2766 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____2766 with
            | (head,args_e) ->
                let uu____2794 =
                  let _0_382 =
                    (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                     in
                  (_0_382, args_e)  in
                (match uu____2794 with
                 | (uu____2809,uu____2810) when head_redex env head ->
                     let _0_383 = whnf env t  in encode_term _0_383 env
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
                     let uu____2894 = encode_term v1 env  in
                     (match uu____2894 with
                      | (v1,decls1) ->
                          let uu____2901 = encode_term v2 env  in
                          (match uu____2901 with
                           | (v2,decls2) ->
                               let _0_384 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2  in
                               (_0_384, (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3300) ->
                     let e0 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_386 =
                                let _0_385 = FStar_List.hd args_e  in
                                [_0_385]  in
                              (head, _0_386)))) None
                         head.FStar_Syntax_Syntax.pos
                        in
                     let e =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_387 = FStar_List.tl args_e  in
                              (e0, _0_387)))) None t0.FStar_Syntax_Syntax.pos
                        in
                     encode_term e env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),(arg,uu____2991)::[]) ->
                     let uu____3009 = encode_term arg env  in
                     (match uu____3009 with
                      | (tm,decls) ->
                          let _0_388 =
                            FStar_SMTEncoding_Util.mkApp ("Reify", [tm])  in
                          (_0_388, decls))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3017),(arg,uu____3019)::[]) -> encode_term arg env
                 | uu____3037 ->
                     let uu____3045 = encode_args args_e env  in
                     (match uu____3045 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3078 = encode_term head env  in
                            match uu____3078 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3604 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3117 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3646  ->
                                                 fun uu____3647  ->
                                                   match (uu____3646,
                                                           uu____3647)
                                                   with
                                                   | ((bv,uu____3661),
                                                      (a,uu____3663)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e
                                             in
                                          let ty =
                                            let _0_389 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right _0_389
                                              (FStar_Syntax_Subst.subst subst)
                                             in
                                          let uu____3192 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3192 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3692 =
                                                   let uu____3696 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3701 =
                                                     let uu____3702 =
                                                       let uu____3703 =
                                                         let uu____3704 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3704 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3703 in
                                                     varops.mk_unique
                                                       uu____3702 in
                                                   (uu____3696,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3701) in
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_392 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        ([[has_type]], cvars,
                                                          has_type)
                                                       in
                                                    let _0_391 =
                                                      Some
                                                        (varops.mk_unique
                                                           (let _0_390 =
                                                              FStar_Util.digest_of_string
                                                                (FStar_SMTEncoding_Term.hash_of_term
                                                                   app_tm)
                                                               in
                                                            Prims.strcat
                                                              "partial_app_typing_"
                                                              _0_390))
                                                       in
                                                    (_0_392,
                                                      (Some
                                                         "Partial app typing"),
                                                      _0_391))
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3223 = lookup_free_var_sym env fv  in
                            match uu____3223 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
                                   in
                                (tm, decls)
                             in
                          let head = FStar_Syntax_Subst.compress head  in
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
                                Some
                                  (let _0_393 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right _0_393 Prims.snd)
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3782,(FStar_Util.Inl t1,uu____3784),uu____3785)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3290,FStar_Util.Inr c,uu____3292) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3313 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3884 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine _0_394
                                  in
                               let uu____3333 =
                                 curried_arrow_formals_comp head_type  in
                               (match uu____3333 with
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
                                     | uu____3910 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3403 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3403 with
            | (bs,body,opening) ->
                let fallback uu____3418 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let _0_395 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (_0_395, [decl])  in
                let is_impure uu___118_3432 =
                  match uu___118_3432 with
                  | FStar_Util.Inl lc ->
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
                  | FStar_Util.Inr (eff,uu____3443) ->
                      let _0_396 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right _0_396 Prims.op_Negation
                   in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let _0_399 =
                        let _0_397 = lc.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening _0_397  in
                      FStar_All.pipe_right _0_399
                        (fun _0_398  -> Some _0_398)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4093 =
                        let uu____4094 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right _0_400 Prims.fst  in
                      (match FStar_Ident.lid_equals eff
                               FStar_Syntax_Const.effect_Tot_lid
                       with
                       | true  ->
                           let _0_402 =
                             FStar_Syntax_Syntax.mk_Total (new_uvar ())  in
                           FStar_All.pipe_right _0_402
                             (fun _0_401  -> Some _0_401)
                       | uu____3487 ->
                           (match FStar_Ident.lid_equals eff
                                    FStar_Syntax_Const.effect_GTot_lid
                            with
                            | true  ->
                                let _0_404 =
                                  FStar_Syntax_Syntax.mk_GTotal (new_uvar ())
                                   in
                                FStar_All.pipe_right _0_404
                                  (fun _0_403  -> Some _0_403)
                            | uu____3490 -> None))
                   in
                (match lopt with
                 | None  ->
                     ((let _0_406 =
                         let _0_405 = FStar_Syntax_Print.term_to_string t0
                            in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s"
                           _0_405
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_406);
                      fallback ())
                 | Some lc ->
                     let uu____3510 = is_impure lc  in
                     (match uu____3510 with
                      | true  -> fallback ()
                      | uu____3513 ->
                          let uu____3514 = encode_binders None bs env  in
                          (match uu____3514 with
                           | (vars,guards,envbody,decls,uu____3529) ->
                               let uu____3536 = encode_term body envbody  in
                               (match uu____3536 with
                                | (body,decls') ->
                                    let key_body =
                                      FStar_SMTEncoding_Util.mkForall
                                        (let _0_408 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (let _0_407 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (_0_407, body))
                                            in
                                         ([], vars, _0_408))
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
                                    let uu____3554 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____3554 with
                                     | Some (t,uu____3569,uu____3570) ->
                                         let _0_410 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_409 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (t, _0_409))
                                            in
                                         (_0_410, [])
                                     | None  ->
                                         let uu____3589 =
                                           is_eta env vars body  in
                                         (match uu____3589 with
                                          | Some t -> (t, [])
                                          | None  ->
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars
                                                 in
                                              let fsym =
                                                varops.mk_unique
                                                  (let _0_411 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.strcat "Tm_abs_"
                                                     _0_411)
                                                 in
                                              let fdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (fsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    None)
                                                 in
                                              let f =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (let _0_412 =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       cvars
                                                      in
                                                   (fsym, _0_412))
                                                 in
                                              let app = mk_Apply f vars  in
                                              let typing_f =
                                                let uu____3610 =
                                                  codomain_eff lc  in
                                                match uu____3610 with
                                                | None  -> []
                                                | Some c ->
                                                    let tfun =
                                                      FStar_Syntax_Util.arrow
                                                        bs c
                                                       in
                                                    let uu____3617 =
                                                      encode_term_pred None
                                                        tfun env f
                                                       in
                                                    (match uu____3617 with
                                                     | (f_has_t,decls'') ->
                                                         let a_name =
                                                           Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                fsym)
                                                            in
                                                         let _0_415 =
                                                           let _0_414 =
                                                             FStar_SMTEncoding_Term.Assume
                                                               (let _0_413 =
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                   in
                                                                (_0_413,
                                                                  a_name,
                                                                  a_name))
                                                              in
                                                           [_0_414]  in
                                                         FStar_List.append
                                                           decls'' _0_415)
                                                 in
                                              let interp_f =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" fsym)
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_417 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_416 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          _0_416))
                                                      in
                                                   (_0_417, a_name, a_name))
                                                 in
                                              let f_decls =
                                                FStar_List.append decls
                                                  (FStar_List.append decls'
                                                     (FStar_List.append
                                                        (fdecl :: typing_f)
                                                        [interp_f]))
                                                 in
                                              (FStar_Util.smap_add env.cache
                                                 tkey_hash
                                                 (fsym, cvar_sorts, f_decls);
                                               (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4355,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4356;
                          FStar_Syntax_Syntax.lbunivs = uu____4357;
                          FStar_Syntax_Syntax.lbtyp = uu____4358;
                          FStar_Syntax_Syntax.lbeff = uu____4359;
                          FStar_Syntax_Syntax.lbdef = uu____4360;_}::uu____4361),uu____4362)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4380;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4382;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4398 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let _0_418 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (_0_418, [decl_e])))
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
              let uu____3749 = encode_term e1 env  in
              match uu____3749 with
              | (ee1,decls1) ->
                  let uu____3756 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____3756 with
                   | (xs,e2) ->
                       let uu____3770 = FStar_List.hd xs  in
                       (match uu____3770 with
                        | (x,uu____3778) ->
                            let env' = push_term_var env x ee1  in
                            let uu____3780 = encode_body e2 env'  in
                            (match uu____3780 with
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
            let uu____3802 = encode_term e env  in
            match uu____3802 with
            | (scr,decls) ->
                let uu____3809 =
                  FStar_List.fold_right
                    (fun b  ->
                       fun uu____3817  ->
                         match uu____3817 with
                         | (else_case,decls) ->
                             let uu____3828 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____3828 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p  in
                                  FStar_List.fold_right
                                    (fun uu____4589  ->
                                       fun uu____4590  ->
                                         match (uu____4589, uu____4590) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr
                                                in
                                             let projections =
                                               pattern.projections scr  in
                                             let env =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4627  ->
                                                         match uu____4627
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env)
                                                in
                                             let uu____3901 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____3916 =
                                                     encode_term w env  in
                                                   (match uu____3916 with
                                                    | (w,decls2) ->
                                                        let _0_421 =
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            (let _0_420 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_419
                                                                    =
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                     in
                                                                  (w, _0_419))
                                                                in
                                                             (guard, _0_420))
                                                           in
                                                        (_0_421, decls2))
                                                in
                                             (match uu____3901 with
                                              | (guard,decls2) ->
                                                  let uu____3931 =
                                                    encode_br br env  in
                                                  (match uu____3931 with
                                                   | (br,decls3) ->
                                                       let _0_422 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case)
                                                          in
                                                       (_0_422,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls))) pats
                    (default_case, decls)
                   in
                (match uu____3809 with
                 | (match_tm,decls) -> (match_tm, decls))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____3962 -> let _0_423 = encode_one_pat env pat  in [_0_423]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____3972 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       match uu____3972 with
       | true  ->
           let _0_424 = FStar_Syntax_Print.pat_to_string pat  in
           FStar_Util.print1 "Encoding pattern %s\n" _0_424
       | uu____3973 -> ());
      (let uu____3974 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____3974 with
       | (vars,pat_term) ->
           let uu____4748 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4007  ->
                     fun v  ->
                       match uu____4007 with
                       | (env,vars) ->
                           let uu____4035 = gen_term_var env v  in
                           (match uu____4035 with
                            | (xx,uu____4047,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, []))
              in
           (match uu____3984 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4094 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_425 = encode_const c  in (scrutinee, _0_425))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        mk_data_tester env
                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4916  ->
                                  match uu____4916 with
                                  | (arg,uu____4922) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_426 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg _0_426))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4166 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4966 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4981 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5003  ->
                                  match uu____5003 with
                                  | (arg,uu____5012) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_427 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg _0_427))
                         in
                      FStar_All.pipe_right _0_428 FStar_List.flatten
                   in
                let pat_term uu____4247 = encode_term pat_term env  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env, pattern)))

and encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____5045 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4269  ->
                fun uu____4270  ->
                  match (uu____4269, uu____4270) with
                  | ((tms,decls),(t,uu____4290)) ->
                      let uu____4301 = encode_term t env  in
                      (match uu____4301 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____4254 with | (l,decls) -> ((FStar_List.rev l), decls)

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
          let list_elements e =
            let uu____4339 = FStar_Syntax_Util.list_elements e  in
            match uu____4339 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____4357 =
              let _0_429 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right _0_429 FStar_Syntax_Util.head_and_args  in
            match uu____4357 with
            | (head,args) ->
                let uu____4397 =
                  let _0_430 =
                    (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                     in
                  (_0_430, args)  in
                (match uu____4397 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5212,uu____5213)::(e,uu____5215)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5246)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____4471 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements p  in
            let smt_pat_or t =
              let uu____4504 =
                let _0_431 = FStar_Syntax_Util.unmeta t  in
                FStar_All.pipe_right _0_431 FStar_Syntax_Util.head_and_args
                 in
              match uu____4504 with
              | (head,args) ->
                  let uu____4542 =
                    let _0_432 =
                      (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                       in
                    (_0_432, args)  in
                  (match uu____4542 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4560)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____4580 -> None)
               in
            match elts with
            | t::[] ->
                let uu____4598 = smt_pat_or t  in
                (match uu____4598 with
                 | Some e ->
                     let _0_434 = list_elements e  in
                     FStar_All.pipe_right _0_434
                       (FStar_List.map
                          (fun branch  ->
                             let _0_433 = list_elements branch  in
                             FStar_All.pipe_right _0_433
                               (FStar_List.map one_pat)))
                 | uu____4641 ->
                     let _0_435 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [_0_435])
            | uu____4669 ->
                let _0_436 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [_0_436]
             in
          let uu____4695 =
            let uu____4711 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____4711 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4739 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____4739 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5596;
                            FStar_Syntax_Syntax.effect_name = uu____5597;
                            FStar_Syntax_Syntax.result_typ = uu____5598;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5600)::(post,uu____5602)::(pats,uu____5604)::[];
                            FStar_Syntax_Syntax.flags = uu____5605;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let _0_437 = lemma_pats pats'  in
                          (binders, pre, post, _0_437)
                      | uu____4828 -> failwith "impos"))
            | uu____4844 -> failwith "Impos"  in
          match uu____4695 with
          | (binders,pre,post,patterns) ->
              let uu____4888 = encode_binders None binders env  in
              (match uu____4888 with
               | (vars,guards,env,decls,uu____4903) ->
                   let uu____4910 =
                     let _0_439 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5778 =
                                 let uu____5783 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____4977  ->
                                           match uu____4977 with
                                           | (t,uu____4984) ->
                                               encode_term t
                                                 (let uu___144_4987 = env  in
                                                  {
                                                    bindings =
                                                      (uu___146_5809.bindings);
                                                    depth =
                                                      (uu___146_5809.depth);
                                                    tcenv =
                                                      (uu___146_5809.tcenv);
                                                    warn =
                                                      (uu___146_5809.warn);
                                                    cache =
                                                      (uu___146_5809.cache);
                                                    nolabels =
                                                      (uu___146_5809.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___144_4987.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right _0_438 FStar_List.unzip
                                  in
                               match uu____4953 with
                               | (pats,decls) -> (pats, decls)))
                        in
                     FStar_All.pipe_right _0_439 FStar_List.unzip  in
                   (match uu____4910 with
                    | (pats,decls') ->
                        let decls' = FStar_List.flatten decls'  in
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
                                           let uu____5873 =
                                             let uu____5874 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               _0_440 e
                                              in
                                           _0_441 :: p))
                               | uu____5033 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5904 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e
                                                    in
                                                 _0_442 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let uu____5912 =
                                           let uu____5913 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             _0_443 tl
                                            in
                                         aux _0_444 vars
                                     | uu____5069 -> pats  in
                                   let _0_445 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux _0_445 vars)
                           in
                        let env =
                          let uu___145_5074 = env  in
                          {
                            bindings = (uu___147_5920.bindings);
                            depth = (uu___147_5920.depth);
                            tcenv = (uu___147_5920.tcenv);
                            warn = (uu___147_5920.warn);
                            cache = (uu___147_5920.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___147_5920.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___145_5074.encode_non_total_function_typ)
                          }  in
                        let uu____5075 =
                          let _0_446 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula _0_446 env  in
                        (match uu____5075 with
                         | (pre,decls'') ->
                             let uu____5082 =
                               let _0_447 = FStar_Syntax_Util.unmeta post  in
                               encode_formula _0_447 env  in
                             (match uu____5082 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let _0_450 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_449 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (let _0_448 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (pre :: guards)
                                               in
                                            (_0_448, post))
                                          in
                                       (pats, vars, _0_449))
                                     in
                                  (_0_450, decls)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5963 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        match uu____5103 with
        | true  ->
            let _0_452 = FStar_Syntax_Print.tag_of_term phi  in
            let _0_451 = FStar_Syntax_Print.term_to_string phi  in
            FStar_Util.print2 "Formula (%s)  %s\n" _0_452 _0_451
        | uu____5104 -> ()  in
      let enc f r l =
        let uu____5992 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5143 = encode_term (Prims.fst x) env  in
                 match uu____5143 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5130 with
        | (decls,args) ->
            let _0_453 =
              let uu___146_5161 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_6023.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_6023.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_453, decls)
         in
      let const_op f r uu____5179 = let _0_454 = f r  in (_0_454, [])  in
      let un_op f l =
        let _0_455 = FStar_List.hd l  in FStar_All.pipe_left f _0_455  in
      let bin_op f uu___119_5209 =
        match uu___119_5209 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5217 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6109 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5253  ->
                 match uu____5253 with
                 | (t,uu____5261) ->
                     let uu____5262 = encode_formula t env  in
                     (match uu____5262 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l
           in
        match uu____5244 with
        | (decls,phis) ->
            let _0_456 =
              let uu___147_5280 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___149_6145.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___149_6145.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_456, decls)
         in
      let eq_op r uu___120_5295 =
        match uu___120_5295 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r [e1; e2]
        | l -> (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l  in
      let mk_imp r uu___121_5380 =
        match uu___121_5380 with
        | (lhs,uu____5384)::(rhs,uu____5386)::[] ->
            let uu____5407 = encode_formula rhs env  in
            (match uu____5407 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6296) ->
                      (l1, decls1)
                  | uu____5419 ->
                      let uu____5420 = encode_formula lhs env  in
                      (match uu____5420 with
                       | (l2,decls2) ->
                           let _0_457 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (_0_457, (FStar_List.append decls1 decls2)))))
        | uu____5428 -> failwith "impossible"  in
      let mk_ite r uu___122_5443 =
        match uu___122_5443 with
        | (guard,uu____5447)::(_then,uu____5449)::(_else,uu____5451)::[] ->
            let uu____5480 = encode_formula guard env  in
            (match uu____5480 with
             | (g,decls1) ->
                 let uu____5487 = encode_formula _then env  in
                 (match uu____5487 with
                  | (t,decls2) ->
                      let uu____5494 = encode_formula _else env  in
                      (match uu____5494 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____5503 -> failwith "impossible"  in
      let unboxInt_l f l =
        f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)  in
      let connectives =
        let _0_470 =
          let _0_458 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
          (FStar_Syntax_Const.and_lid, _0_458)  in
        let _0_469 =
          let _0_468 =
            let _0_459 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
            (FStar_Syntax_Const.or_lid, _0_459)  in
          let _0_467 =
            let _0_466 =
              let _0_465 =
                let _0_460 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)
                   in
                (FStar_Syntax_Const.iff_lid, _0_460)  in
              let _0_464 =
                let _0_463 =
                  let _0_462 =
                    let _0_461 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, _0_461)  in
                  [_0_462;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: _0_463  in
              _0_465 :: _0_464  in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: _0_466  in
          _0_468 :: _0_467  in
        _0_470 :: _0_469  in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____5705 = encode_formula phi' env  in
            (match uu____5705 with
             | (phi,decls) ->
                 let _0_471 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r
                    in
                 (_0_471, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____5712 ->
            let _0_472 = FStar_Syntax_Util.unmeta phi  in
            encode_formula _0_472 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6744 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____5745 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6752;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6754;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____5771 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____5771 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head  in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6802::(x,uu____6804)::(t,uu____6806)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____5841 = encode_term x env  in
                 (match uu____5841 with
                  | (x,decls) ->
                      let uu____5848 = encode_term t env  in
                      (match uu____5848 with
                       | (t,decls') ->
                           let _0_473 = FStar_SMTEncoding_Term.mk_HasType x t
                              in
                           (_0_473, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6858)::(msg,uu____6860)::(phi2,uu____6862)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____5896 =
                   let _0_475 =
                     (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
                      in
                   let _0_474 =
                     (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
                      in
                   (_0_475, _0_474)  in
                 (match uu____5896 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6911))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r
                         in
                      fallback phi
                  | uu____5919 -> fallback phi)
             | uu____5922 when head_redex env head ->
                 let _0_476 = whnf env phi  in encode_formula _0_476 env
             | uu____5930 ->
                 let uu____5938 = encode_term phi env  in
                 (match uu____5938 with
                  | (tt,decls) ->
                      let uu____6954 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___148_5945 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___150_6955.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___150_6955.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (_0_477, decls)))
        | uu____5948 ->
            let uu____5949 = encode_term phi env  in
            (match uu____5949 with
             | (tt,decls) ->
                 let uu____6966 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___149_5956 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___151_6967.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___151_6967.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (_0_478, decls))
         in
      let encode_q_body env bs ps body =
        let uu____5983 = encode_binders None bs env  in
        match uu____5983 with
        | (vars,guards,env,decls,uu____6005) ->
            let uu____6012 =
              let _0_480 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7053 =
                          let uu____7058 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7072  ->
                                    match uu____7072 with
                                    | (t,uu____7078) ->
                                        encode_term t
                                          (let uu___150_6076 = env  in
                                           {
                                             bindings =
                                               (uu___152_7079.bindings);
                                             depth = (uu___152_7079.depth);
                                             tcenv = (uu___152_7079.tcenv);
                                             warn = (uu___152_7079.warn);
                                             cache = (uu___152_7079.cache);
                                             nolabels =
                                               (uu___152_7079.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___150_6076.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right _0_479 FStar_List.unzip  in
                        match uu____6047 with
                        | (p,decls) -> (p, (FStar_List.flatten decls))))
                 in
              FStar_All.pipe_right _0_480 FStar_List.unzip  in
            (match uu____6012 with
             | (pats,decls') ->
                 let uu____6110 = encode_formula body env  in
                 (match uu____6110 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7150;
                             FStar_SMTEncoding_Term.rng = uu____7151;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6138 -> guards  in
                      let _0_481 = FStar_SMTEncoding_Util.mk_and_l guards  in
                      (vars, pats, _0_481, body,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug phi;
      (let phi = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7196  ->
                   match uu____7196 with
                   | (x,uu____7200) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let _0_483 = FStar_Syntax_Free.names hd  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let _0_482 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out _0_482) _0_483 tl
                in
             let uu____6188 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6200  ->
                       match uu____6200 with
                       | (b,uu____6204) ->
                           Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
                in
             (match uu____6188 with
              | None  -> ()
              | Some (x,uu____7235) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl
                     in
                  let _0_485 =
                    let _0_484 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      _0_484
                     in
                  FStar_Errors.warn pos _0_485)
          in
       let uu____6218 = FStar_Syntax_Util.destruct_typ_as_formula phi  in
       match uu____6218 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7253 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____6260  ->
                     match uu____6260 with
                     | (l,uu____6270) -> FStar_Ident.lid_equals op l))
              in
           (match uu____6224 with
            | None  -> fallback phi
            | Some (uu____6293,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6322 = encode_q_body env vars pats body  in
             match uu____6322 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let _0_487 =
                     let _0_486 = FStar_SMTEncoding_Util.mkImp (guard, body)
                        in
                     (pats, vars, _0_486)  in
                   FStar_SMTEncoding_Term.mkForall _0_487
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6359 = encode_q_body env vars pats body  in
             match uu____6359 with
             | (vars,pats,guard,body,decls) ->
                 let _0_490 =
                   let _0_489 =
                     let _0_488 = FStar_SMTEncoding_Util.mkAnd (guard, body)
                        in
                     (pats, vars, _0_488)  in
                   FStar_SMTEncoding_Term.mkExists _0_489
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (_0_490, decls))))

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
  let uu____6432 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____6432 with
  | (asym,a) ->
      let uu____6437 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____6437 with
       | (xsym,x) ->
           let uu____6442 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____6442 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_491 =
                         FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                          in
                       (x, _0_491, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  let xtok = Prims.strcat x "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    FStar_SMTEncoding_Util.mkApp
                      (let _0_492 =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                          in
                       (x, _0_492))
                     in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok vars  in
                  let _0_502 =
                    let _0_501 =
                      let _0_500 =
                        let _0_499 =
                          FStar_SMTEncoding_Term.Assume
                            (let _0_494 =
                               FStar_SMTEncoding_Util.mkForall
                                 (let _0_493 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, _0_493))
                                in
                             (_0_494, None,
                               (Some (Prims.strcat "primitive_" x))))
                           in
                        let _0_498 =
                          let _0_497 =
                            FStar_SMTEncoding_Term.Assume
                              (let _0_496 =
                                 FStar_SMTEncoding_Util.mkForall
                                   (let _0_495 =
                                      FStar_SMTEncoding_Util.mkEq
                                        (xtok_app, xapp)
                                       in
                                    ([[xtok_app]], vars, _0_495))
                                  in
                               (_0_496, (Some "Name-token correspondence"),
                                 (Some
                                    (Prims.strcat "token_correspondence_" x))))
                             in
                          [_0_497]  in
                        _0_499 :: _0_498  in
                      xtok_decl :: _0_500  in
                    xname_decl :: _0_501  in
                  (xtok, _0_502)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims =
                  let _0_598 =
                    let _0_505 =
                      let _0_504 =
                        let _0_503 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          _0_503
                         in
                      quant axy _0_504  in
                    (FStar_Syntax_Const.op_Eq, _0_505)  in
                  let _0_597 =
                    let _0_596 =
                      let _0_508 =
                        let _0_507 =
                          let _0_506 =
                            FStar_SMTEncoding_Util.mkNot
                              (FStar_SMTEncoding_Util.mkEq (x, y))
                             in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            _0_506
                           in
                        quant axy _0_507  in
                      (FStar_Syntax_Const.op_notEq, _0_508)  in
                    let _0_595 =
                      let _0_594 =
                        let _0_513 =
                          let _0_512 =
                            let _0_511 =
                              FStar_SMTEncoding_Util.mkLT
                                (let _0_510 =
                                   FStar_SMTEncoding_Term.unboxInt x  in
                                 let _0_509 =
                                   FStar_SMTEncoding_Term.unboxInt y  in
                                 (_0_510, _0_509))
                               in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool _0_511
                             in
                          quant xy _0_512  in
                        (FStar_Syntax_Const.op_LT, _0_513)  in
                      let _0_593 =
                        let _0_592 =
                          let _0_518 =
                            let _0_517 =
                              let _0_516 =
                                FStar_SMTEncoding_Util.mkLTE
                                  (let _0_515 =
                                     FStar_SMTEncoding_Term.unboxInt x  in
                                   let _0_514 =
                                     FStar_SMTEncoding_Term.unboxInt y  in
                                   (_0_515, _0_514))
                                 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool _0_516
                               in
                            quant xy _0_517  in
                          (FStar_Syntax_Const.op_LTE, _0_518)  in
                        let _0_591 =
                          let _0_590 =
                            let _0_523 =
                              let _0_522 =
                                let _0_521 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_520 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_519 =
                                       FStar_SMTEncoding_Term.unboxInt y  in
                                     (_0_520, _0_519))
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool _0_521
                                 in
                              quant xy _0_522  in
                            (FStar_Syntax_Const.op_GT, _0_523)  in
                          let _0_589 =
                            let _0_588 =
                              let _0_528 =
                                let _0_527 =
                                  let _0_526 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_525 =
                                         FStar_SMTEncoding_Term.unboxInt x
                                          in
                                       let _0_524 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       (_0_525, _0_524))
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool _0_526
                                   in
                                quant xy _0_527  in
                              (FStar_Syntax_Const.op_GTE, _0_528)  in
                            let _0_587 =
                              let _0_586 =
                                let _0_533 =
                                  let _0_532 =
                                    let _0_531 =
                                      FStar_SMTEncoding_Util.mkSub
                                        (let _0_530 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         let _0_529 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         (_0_530, _0_529))
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt _0_531
                                     in
                                  quant xy _0_532  in
                                (FStar_Syntax_Const.op_Subtraction, _0_533)
                                 in
                              let _0_585 =
                                let _0_584 =
                                  let _0_536 =
                                    let _0_535 =
                                      let _0_534 =
                                        FStar_SMTEncoding_Util.mkMinus
                                          (FStar_SMTEncoding_Term.unboxInt x)
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt _0_534
                                       in
                                    quant qx _0_535  in
                                  (FStar_Syntax_Const.op_Minus, _0_536)  in
                                let _0_583 =
                                  let _0_582 =
                                    let _0_541 =
                                      let _0_540 =
                                        let _0_539 =
                                          FStar_SMTEncoding_Util.mkAdd
                                            (let _0_538 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 x
                                                in
                                             let _0_537 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 y
                                                in
                                             (_0_538, _0_537))
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          _0_539
                                         in
                                      quant xy _0_540  in
                                    (FStar_Syntax_Const.op_Addition, _0_541)
                                     in
                                  let _0_581 =
                                    let _0_580 =
                                      let _0_546 =
                                        let _0_545 =
                                          let _0_544 =
                                            FStar_SMTEncoding_Util.mkMul
                                              (let _0_543 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   x
                                                  in
                                               let _0_542 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   y
                                                  in
                                               (_0_543, _0_542))
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            _0_544
                                           in
                                        quant xy _0_545  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        _0_546)
                                       in
                                    let _0_579 =
                                      let _0_578 =
                                        let _0_551 =
                                          let _0_550 =
                                            let _0_549 =
                                              FStar_SMTEncoding_Util.mkDiv
                                                (let _0_548 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     x
                                                    in
                                                 let _0_547 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     y
                                                    in
                                                 (_0_548, _0_547))
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              _0_549
                                             in
                                          quant xy _0_550  in
                                        (FStar_Syntax_Const.op_Division,
                                          _0_551)
                                         in
                                      let _0_577 =
                                        let _0_576 =
                                          let _0_556 =
                                            let _0_555 =
                                              let _0_554 =
                                                FStar_SMTEncoding_Util.mkMod
                                                  (let _0_553 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       x
                                                      in
                                                   let _0_552 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       y
                                                      in
                                                   (_0_553, _0_552))
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                _0_554
                                               in
                                            quant xy _0_555  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            _0_556)
                                           in
                                        let _0_575 =
                                          let _0_574 =
                                            let _0_561 =
                                              let _0_560 =
                                                let _0_559 =
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    (let _0_558 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         x
                                                        in
                                                     let _0_557 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         y
                                                        in
                                                     (_0_558, _0_557))
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  _0_559
                                                 in
                                              quant xy _0_560  in
                                            (FStar_Syntax_Const.op_And,
                                              _0_561)
                                             in
                                          let _0_573 =
                                            let _0_572 =
                                              let _0_566 =
                                                let _0_565 =
                                                  let _0_564 =
                                                    FStar_SMTEncoding_Util.mkOr
                                                      (let _0_563 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           x
                                                          in
                                                       let _0_562 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           y
                                                          in
                                                       (_0_563, _0_562))
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    _0_564
                                                   in
                                                quant xy _0_565  in
                                              (FStar_Syntax_Const.op_Or,
                                                _0_566)
                                               in
                                            let _0_571 =
                                              let _0_570 =
                                                let _0_569 =
                                                  let _0_568 =
                                                    let _0_567 =
                                                      FStar_SMTEncoding_Util.mkNot
                                                        (FStar_SMTEncoding_Term.unboxBool
                                                           x)
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      _0_567
                                                     in
                                                  quant qx _0_568  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  _0_569)
                                                 in
                                              [_0_570]  in
                                            _0_572 :: _0_571  in
                                          _0_574 :: _0_573  in
                                        _0_576 :: _0_575  in
                                      _0_578 :: _0_577  in
                                    _0_580 :: _0_579  in
                                  _0_582 :: _0_581  in
                                _0_584 :: _0_583  in
                              _0_586 :: _0_585  in
                            _0_588 :: _0_587  in
                          _0_590 :: _0_589  in
                        _0_592 :: _0_591  in
                      _0_594 :: _0_593  in
                    _0_596 :: _0_595  in
                  _0_598 :: _0_597  in
                let mk l v =
                  let _0_600 =
                    let _0_599 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____6788  ->
                              match uu____6788 with
                              | (l',uu____6797) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right _0_599
                      (FStar_Option.map
                         (fun uu____6818  ->
                            match uu____6818 with | (uu____6829,b) -> b v))
                     in
                  FStar_All.pipe_right _0_600 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____6863  ->
                          match uu____6863 with
                          | (l',uu____6872) -> FStar_Ident.lid_equals l l'))
                   in
                { mk; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____6895 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____6895 with
      | (xxsym,xx) ->
          let uu____6900 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____6900 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               FStar_SMTEncoding_Term.Assume
                 (let _0_606 =
                    FStar_SMTEncoding_Util.mkForall
                      (let _0_603 =
                         FStar_SMTEncoding_Util.mkImp
                           (let _0_602 =
                              FStar_SMTEncoding_Util.mkEq
                                (let _0_601 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, _0_601))
                               in
                            (xx_has_type, _0_602))
                          in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         _0_603))
                     in
                  let _0_605 =
                    Some
                      (varops.mk_unique
                         (let _0_604 = FStar_Util.digest_of_string tapp_hash
                             in
                          Prims.strcat "pretyping_" _0_604))
                     in
                  (_0_606, (Some "pretyping"), _0_605)))
  
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
    let _0_613 =
      FStar_SMTEncoding_Term.Assume
        (let _0_607 =
           FStar_SMTEncoding_Term.mk_HasType
             FStar_SMTEncoding_Term.mk_Term_unit tt
            in
         (_0_607, (Some "unit typing"), (Some "unit_typing")))
       in
    let _0_612 =
      let _0_611 =
        FStar_SMTEncoding_Term.Assume
          (let _0_610 =
             mkForall_fuel
               (let _0_609 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_608 =
                       FStar_SMTEncoding_Util.mkEq
                         (x, FStar_SMTEncoding_Term.mk_Term_unit)
                        in
                     (typing_pred, _0_608))
                   in
                ([[typing_pred]], [xx], _0_609))
              in
           (_0_610, (Some "unit inversion"), (Some "unit_inversion")))
         in
      [_0_611]  in
    _0_613 :: _0_612  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_625 =
      FStar_SMTEncoding_Term.Assume
        (let _0_619 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_618 =
                let _0_615 =
                  let _0_614 = FStar_SMTEncoding_Term.boxBool b  in [_0_614]
                   in
                [_0_615]  in
              let _0_617 =
                let _0_616 = FStar_SMTEncoding_Term.boxBool b  in
                FStar_SMTEncoding_Term.mk_HasType _0_616 tt  in
              (_0_618, [bb], _0_617))
            in
         (_0_619, (Some "bool typing"), (Some "bool_typing")))
       in
    let _0_624 =
      let _0_623 =
        FStar_SMTEncoding_Term.Assume
          (let _0_622 =
             mkForall_fuel
               (let _0_621 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_620 =
                       FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                     (typing_pred, _0_620))
                   in
                ([[typing_pred]], [xx], _0_621))
              in
           (_0_622, (Some "bool inversion"), (Some "bool_inversion")))
         in
      [_0_623]  in
    _0_625 :: _0_624  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let _0_632 =
        FStar_SMTEncoding_Util.mkApp
          (let _0_631 =
             let _0_630 =
               let _0_629 =
                 let _0_628 = FStar_SMTEncoding_Term.boxInt a  in
                 let _0_627 =
                   let _0_626 = FStar_SMTEncoding_Term.boxInt b  in [_0_626]
                    in
                 _0_628 :: _0_627  in
               tt :: _0_629  in
             tt :: _0_630  in
           ("Prims.Precedes", _0_631))
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_632  in
    let precedes_y_x =
      let _0_633 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_633  in
    let _0_663 =
      FStar_SMTEncoding_Term.Assume
        (let _0_639 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_638 =
                let _0_635 =
                  let _0_634 = FStar_SMTEncoding_Term.boxInt b  in [_0_634]
                   in
                [_0_635]  in
              let _0_637 =
                let _0_636 = FStar_SMTEncoding_Term.boxInt b  in
                FStar_SMTEncoding_Term.mk_HasType _0_636 tt  in
              (_0_638, [bb], _0_637))
            in
         (_0_639, (Some "int typing"), (Some "int_typing")))
       in
    let _0_662 =
      let _0_661 =
        FStar_SMTEncoding_Term.Assume
          (let _0_642 =
             mkForall_fuel
               (let _0_641 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_640 = FStar_SMTEncoding_Term.mk_tester "BoxInt" x
                        in
                     (typing_pred, _0_640))
                   in
                ([[typing_pred]], [xx], _0_641))
              in
           (_0_642, (Some "int inversion"), (Some "int_inversion")))
         in
      let _0_660 =
        let _0_659 =
          FStar_SMTEncoding_Term.Assume
            (let _0_658 =
               mkForall_fuel
                 (let _0_657 =
                    FStar_SMTEncoding_Util.mkImp
                      (let _0_656 =
                         FStar_SMTEncoding_Util.mk_and_l
                           (let _0_655 =
                              let _0_654 =
                                let _0_653 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_644 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_643 =
                                       FStar_SMTEncoding_Util.mkInteger'
                                         (Prims.parse_int "0")
                                        in
                                     (_0_644, _0_643))
                                   in
                                let _0_652 =
                                  let _0_651 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_646 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       let _0_645 =
                                         FStar_SMTEncoding_Util.mkInteger'
                                           (Prims.parse_int "0")
                                          in
                                       (_0_646, _0_645))
                                     in
                                  let _0_650 =
                                    let _0_649 =
                                      FStar_SMTEncoding_Util.mkLT
                                        (let _0_648 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         let _0_647 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         (_0_648, _0_647))
                                       in
                                    [_0_649]  in
                                  _0_651 :: _0_650  in
                                _0_653 :: _0_652  in
                              typing_pred_y :: _0_654  in
                            typing_pred :: _0_655)
                          in
                       (_0_656, precedes_y_x))
                     in
                  ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                    _0_657))
                in
             (_0_658, (Some "well-founded ordering on nat (alt)"),
               (Some "well-founded-ordering-on-nat")))
           in
        [_0_659]  in
      _0_661 :: _0_660  in
    _0_663 :: _0_662  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_675 =
      FStar_SMTEncoding_Term.Assume
        (let _0_669 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_668 =
                let _0_665 =
                  let _0_664 = FStar_SMTEncoding_Term.boxString b  in
                  [_0_664]  in
                [_0_665]  in
              let _0_667 =
                let _0_666 = FStar_SMTEncoding_Term.boxString b  in
                FStar_SMTEncoding_Term.mk_HasType _0_666 tt  in
              (_0_668, [bb], _0_667))
            in
         (_0_669, (Some "string typing"), (Some "string_typing")))
       in
    let _0_674 =
      let _0_673 =
        FStar_SMTEncoding_Term.Assume
          (let _0_672 =
             mkForall_fuel
               (let _0_671 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_670 =
                       FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                     (typing_pred, _0_670))
                   in
                ([[typing_pred]], [xx], _0_671))
              in
           (_0_672, (Some "string inversion"), (Some "string_inversion")))
         in
      [_0_673]  in
    _0_675 :: _0_674  in
  let mk_ref env reft_name uu____7120 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      FStar_SMTEncoding_Util.mkApp
        (let _0_677 =
           let _0_676 = FStar_SMTEncoding_Util.mkFreeV aa  in [_0_676]  in
         (reft_name, _0_677))
       in
    let refb =
      FStar_SMTEncoding_Util.mkApp
        (let _0_679 =
           let _0_678 = FStar_SMTEncoding_Util.mkFreeV bb  in [_0_678]  in
         (reft_name, _0_679))
       in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let _0_692 =
      FStar_SMTEncoding_Term.Assume
        (let _0_682 =
           mkForall_fuel
             (let _0_681 =
                FStar_SMTEncoding_Util.mkImp
                  (let _0_680 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                      in
                   (typing_pred, _0_680))
                 in
              ([[typing_pred]], [xx; aa], _0_681))
            in
         (_0_682, (Some "ref inversion"), (Some "ref_inversion")))
       in
    let _0_691 =
      let _0_690 =
        FStar_SMTEncoding_Term.Assume
          (let _0_689 =
             let _0_688 =
               let _0_687 =
                 FStar_SMTEncoding_Util.mkImp
                   (let _0_686 =
                      FStar_SMTEncoding_Util.mkAnd
                        (typing_pred, typing_pred_b)
                       in
                    let _0_685 =
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_684 = FStar_SMTEncoding_Util.mkFreeV aa  in
                         let _0_683 = FStar_SMTEncoding_Util.mkFreeV bb  in
                         (_0_684, _0_683))
                       in
                    (_0_686, _0_685))
                  in
               ([[typing_pred; typing_pred_b]], [xx; aa; bb], _0_687)  in
             mkForall_fuel' (Prims.parse_int "2") _0_688  in
           (_0_689, (Some "ref typing is injective"),
             (Some "ref_injectivity")))
         in
      [_0_690]  in
    _0_692 :: _0_691  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let _0_694 =
      FStar_SMTEncoding_Term.Assume
        (let _0_693 =
           FStar_SMTEncoding_Util.mkIff
             (FStar_SMTEncoding_Util.mkFalse, valid)
            in
         (_0_693, (Some "False interpretation"), (Some "false_interp")))
       in
    [_0_694]  in
  let mk_and_interp env conj uu____7205 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_696 =
           let _0_695 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
           [_0_695]  in
         ("Valid", _0_696))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_700 =
      FStar_SMTEncoding_Term.Assume
        (let _0_699 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_698 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_697 =
                     FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                   (_0_697, valid))
                 in
              ([[valid]], [aa; bb], _0_698))
            in
         (_0_699, (Some "/\\ interpretation"), (Some "l_and-interp")))
       in
    [_0_700]  in
  let mk_or_interp env disj uu____7245 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_702 =
           let _0_701 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
           [_0_701]  in
         ("Valid", _0_702))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_706 =
      FStar_SMTEncoding_Term.Assume
        (let _0_705 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_704 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_703 =
                     FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                   (_0_703, valid))
                 in
              ([[valid]], [aa; bb], _0_704))
            in
         (_0_705, (Some "\\/ interpretation"), (Some "l_or-interp")))
       in
    [_0_706]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let y = FStar_SMTEncoding_Util.mkFreeV yy  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_708 =
           let _0_707 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y])  in
           [_0_707]  in
         ("Valid", _0_708))
       in
    let _0_712 =
      FStar_SMTEncoding_Term.Assume
        (let _0_711 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_710 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_709 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_709, valid))
                 in
              ([[valid]], [aa; xx; yy], _0_710))
            in
         (_0_711, (Some "Eq2 interpretation"), (Some "eq2-interp")))
       in
    [_0_712]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let y = FStar_SMTEncoding_Util.mkFreeV yy  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_714 =
           let _0_713 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y])  in
           [_0_713]  in
         ("Valid", _0_714))
       in
    let _0_718 =
      FStar_SMTEncoding_Term.Assume
        (let _0_717 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_716 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_715 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_715, valid))
                 in
              ([[valid]], [aa; bb; xx; yy], _0_716))
            in
         (_0_717, (Some "Eq3 interpretation"), (Some "eq3-interp")))
       in
    [_0_718]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_720 =
           let _0_719 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
           [_0_719]  in
         ("Valid", _0_720))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_724 =
      FStar_SMTEncoding_Term.Assume
        (let _0_723 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_722 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_721 =
                     FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                   (_0_721, valid))
                 in
              ([[valid]], [aa; bb], _0_722))
            in
         (_0_723, (Some "==> interpretation"), (Some "l_imp-interp")))
       in
    [_0_724]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_726 =
           let _0_725 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
           [_0_725]  in
         ("Valid", _0_726))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_730 =
      FStar_SMTEncoding_Term.Assume
        (let _0_729 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_728 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_727 =
                     FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                   (_0_727, valid))
                 in
              ([[valid]], [aa; bb], _0_728))
            in
         (_0_729, (Some "<==> interpretation"), (Some "l_iff-interp")))
       in
    [_0_730]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_732 =
           let _0_731 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
           [_0_731]  in
         ("Valid", _0_732))
       in
    let not_valid_a =
      let _0_733 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_733  in
    let _0_736 =
      FStar_SMTEncoding_Term.Assume
        (let _0_735 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_734 = FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)
                 in
              ([[valid]], [aa], _0_734))
            in
         (_0_735, (Some "not interpretation"), (Some "l_not-interp")))
       in
    [_0_736]  in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_738 =
           let _0_737 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b])  in
           [_0_737]  in
         ("Valid", _0_738))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_740 =
           let _0_739 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_739]
            in
         ("Valid", _0_740))
       in
    let _0_749 =
      FStar_SMTEncoding_Term.Assume
        (let _0_748 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_747 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_746 =
                     FStar_SMTEncoding_Util.mkForall
                       (let _0_745 =
                          let _0_742 =
                            let _0_741 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_741]  in
                          [_0_742]  in
                        let _0_744 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_743 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_743, valid_b_x))
                           in
                        (_0_745, [xx], _0_744))
                      in
                   (_0_746, valid))
                 in
              ([[valid]], [aa; bb], _0_747))
            in
         (_0_748, (Some "forall interpretation"), (Some "forall-interp")))
       in
    [_0_749]  in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_751 =
           let _0_750 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b])  in
           [_0_750]  in
         ("Valid", _0_751))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_753 =
           let _0_752 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_752]
            in
         ("Valid", _0_753))
       in
    let _0_762 =
      FStar_SMTEncoding_Term.Assume
        (let _0_761 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_760 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_759 =
                     FStar_SMTEncoding_Util.mkExists
                       (let _0_758 =
                          let _0_755 =
                            let _0_754 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_754]  in
                          [_0_755]  in
                        let _0_757 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_756 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_756, valid_b_x))
                           in
                        (_0_758, [xx], _0_757))
                      in
                   (_0_759, valid))
                 in
              ([[valid]], [aa; bb], _0_760))
            in
         (_0_761, (Some "exists interpretation"), (Some "exists-interp")))
       in
    [_0_762]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let _0_765 =
      FStar_SMTEncoding_Term.Assume
        (let _0_764 =
           FStar_SMTEncoding_Term.mk_HasTypeZ
             FStar_SMTEncoding_Term.mk_Range_const range_ty
            in
         let _0_763 = Some (varops.mk_unique "typing_range_const")  in
         (_0_764, (Some "Range_const typing"), _0_763))
       in
    [_0_765]  in
  let prims =
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
          let uu____9925 =
            FStar_Util.find_opt
              (fun uu____7876  ->
                 match uu____7876 with
                 | (l,uu____7886) -> FStar_Ident.lid_equals l t) prims
             in
          match uu____7858 with
          | None  -> []
          | Some (uu____7908,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7945 = encode_function_type_as_formula None None t env  in
        match uu____7945 with
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
            let uu____7978 =
              (let _0_766 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm  in
               FStar_All.pipe_left Prims.op_Negation _0_766) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            match uu____7978 with
            | true  ->
                let uu____7982 = new_term_constant_and_tok_from_lid env lid
                   in
                (match uu____7982 with
                 | (vname,vtok,env) ->
                     let arg_sorts =
                       let uu____7994 =
                         (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                          in
                       match uu____7994 with
                       | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7997) ->
                           FStar_All.pipe_right binders
                             (FStar_List.map
                                (fun uu____8014  ->
                                   FStar_SMTEncoding_Term.Term_sort))
                       | uu____8017 -> []  in
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
                     ([d; dd], env))
            | uu____8025 ->
                let uu____8026 = prims.is lid  in
                (match uu____8026 with
                 | true  ->
                     let vname = varops.new_fvar lid  in
                     let uu____8031 = prims.mk lid vname  in
                     (match uu____8031 with
                      | (tok,definition) ->
                          let env = push_free_var env lid vname (Some tok)
                             in
                          (definition, env))
                 | uu____8044 ->
                     let encode_non_total_function_typ =
                       lid.FStar_Ident.nsstr <> "Prims"  in
                     let uu____8046 =
                       let uu____8052 = curried_arrow_formals_comp t_norm  in
                       match uu____8052 with
                       | (args,comp) ->
                           (match encode_non_total_function_typ with
                            | true  ->
                                let _0_767 =
                                  FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                    env.tcenv comp
                                   in
                                (args, _0_767)
                            | uu____8070 ->
                                (args,
                                  (None,
                                    (FStar_Syntax_Util.comp_result comp))))
                        in
                     (match uu____8046 with
                      | (formals,(pre_opt,res_t)) ->
                          let uu____8090 =
                            new_term_constant_and_tok_from_lid env lid  in
                          (match uu____8090 with
                           | (vname,vtok,env) ->
                               let vtok_tm =
                                 match formals with
                                 | [] ->
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (vname,
                                         FStar_SMTEncoding_Term.Term_sort)
                                 | uu____8103 ->
                                     FStar_SMTEncoding_Util.mkApp (vtok, [])
                                  in
                               let mk_disc_proj_axioms guard encoded_res_t
                                 vapp vars =
                                 FStar_All.pipe_right quals
                                   (FStar_List.collect
                                      (fun uu___123_8127  ->
                                         match uu___123_8127 with
                                         | FStar_Syntax_Syntax.Discriminator
                                             d ->
                                             let uu____8130 =
                                               FStar_Util.prefix vars  in
                                             (match uu____8130 with
                                              | (uu____8141,(xxsym,uu____8143))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  let _0_772 =
                                                    FStar_SMTEncoding_Term.Assume
                                                      (let _0_771 =
                                                         FStar_SMTEncoding_Util.mkForall
                                                           (let _0_770 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (let _0_769 =
                                                                   let _0_768
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    (escape
                                                                    d.FStar_Ident.str)
                                                                    xx  in
                                                                   FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    _0_768
                                                                    in
                                                                 (vapp,
                                                                   _0_769))
                                                               in
                                                            ([[vapp]], vars,
                                                              _0_770))
                                                          in
                                                       (_0_771,
                                                         (Some
                                                            "Discriminator equation"),
                                                         (Some
                                                            (Prims.strcat
                                                               "disc_equation_"
                                                               (escape
                                                                  d.FStar_Ident.str)))))
                                                     in
                                                  [_0_772])
                                         | FStar_Syntax_Syntax.Projector
                                             (d,f) ->
                                             let uu____8164 =
                                               FStar_Util.prefix vars  in
                                             (match uu____8164 with
                                              | (uu____8175,(xxsym,uu____8177))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
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
                                                    }  in
                                                  let tp_name =
                                                    mk_term_projector_name d
                                                      f
                                                     in
                                                  let prim_app =
                                                    FStar_SMTEncoding_Util.mkApp
                                                      (tp_name, [xx])
                                                     in
                                                  let _0_775 =
                                                    FStar_SMTEncoding_Term.Assume
                                                      (let _0_774 =
                                                         FStar_SMTEncoding_Util.mkForall
                                                           (let _0_773 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vapp,
                                                                  prim_app)
                                                               in
                                                            ([[vapp]], vars,
                                                              _0_773))
                                                          in
                                                       (_0_774,
                                                         (Some
                                                            "Projector equation"),
                                                         (Some
                                                            (Prims.strcat
                                                               "proj_equation_"
                                                               tp_name))))
                                                     in
                                                  [_0_775])
                                         | uu____8200 -> []))
                                  in
                               let uu____8201 =
                                 encode_binders None formals env  in
                               (match uu____8201 with
                                | (vars,guards,env',decls1,uu____8217) ->
                                    let uu____8224 =
                                      match pre_opt with
                                      | None  ->
                                          let _0_776 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards
                                             in
                                          (_0_776, decls1)
                                      | Some p ->
                                          let uu____8230 =
                                            encode_formula p env'  in
                                          (match uu____8230 with
                                           | (g,ds) ->
                                               let _0_777 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (g :: guards)
                                                  in
                                               (_0_777,
                                                 (FStar_List.append decls1 ds)))
                                       in
                                    (match uu____8224 with
                                     | (guard,decls1) ->
                                         let vtok_app = mk_Apply vtok_tm vars
                                            in
                                         let vapp =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_778 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  vars
                                                 in
                                              (vname, _0_778))
                                            in
                                         let uu____8248 =
                                           let vname_decl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (let _0_779 =
                                                  FStar_All.pipe_right
                                                    formals
                                                    (FStar_List.map
                                                       (fun uu____8258  ->
                                                          FStar_SMTEncoding_Term.Term_sort))
                                                   in
                                                (vname, _0_779,
                                                  FStar_SMTEncoding_Term.Term_sort,
                                                  None))
                                              in
                                           let uu____8261 =
                                             let env =
                                               let uu___151_8265 = env  in
                                               {
                                                 bindings =
                                                   (uu___151_8265.bindings);
                                                 depth =
                                                   (uu___151_8265.depth);
                                                 tcenv =
                                                   (uu___151_8265.tcenv);
                                                 warn = (uu___151_8265.warn);
                                                 cache =
                                                   (uu___151_8265.cache);
                                                 nolabels =
                                                   (uu___151_8265.nolabels);
                                                 use_zfuel_name =
                                                   (uu___151_8265.use_zfuel_name);
                                                 encode_non_total_function_typ
                                               }  in
                                             let uu____8266 =
                                               Prims.op_Negation
                                                 (head_normal env tt)
                                                in
                                             match uu____8266 with
                                             | true  ->
                                                 encode_term_pred None tt env
                                                   vtok_tm
                                             | uu____8269 ->
                                                 encode_term_pred None t_norm
                                                   env vtok_tm
                                              in
                                           match uu____8261 with
                                           | (tok_typing,decls2) ->
                                               let tok_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10445 ->
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        (Prims.strcat
                                                           "function_token_typing_"
                                                           vname)))
                                                  in
                                               let uu____8278 =
                                                 match formals with
                                                 | [] ->
                                                     let _0_783 =
                                                       let _0_782 =
                                                         let _0_781 =
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                             (vname,
                                                               FStar_SMTEncoding_Term.Term_sort)
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_780  ->
                                                              Some _0_780)
                                                           _0_781
                                                          in
                                                       push_free_var env lid
                                                         vname _0_782
                                                        in
                                                     ((FStar_List.append
                                                         decls2 [tok_typing]),
                                                       _0_783)
                                                 | uu____8289 ->
                                                     let vtok_decl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (vtok, [],
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None)
                                                        in
                                                     let vtok_fresh =
                                                       let _0_784 =
                                                         varops.next_id ()
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_token
                                                         (vtok,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                         _0_784
                                                        in
                                                     let name_tok_corr =
                                                       FStar_SMTEncoding_Term.Assume
                                                         (let _0_786 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              (let _0_785 =
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   (vtok_app,
                                                                    vapp)
                                                                  in
                                                               ([[vtok_app];
                                                                [vapp]],
                                                                 vars,
                                                                 _0_785))
                                                             in
                                                          (_0_786,
                                                            (Some
                                                               "Name-token correspondence"),
                                                            (Some
                                                               (Prims.strcat
                                                                  "token_correspondence_"
                                                                  vname))))
                                                        in
                                                     ((FStar_List.append
                                                         decls2
                                                         [vtok_decl;
                                                         vtok_fresh;
                                                         name_tok_corr;
                                                         tok_typing]), env)
                                                  in
                                               (match uu____8278 with
                                                | (tok_decl,env) ->
                                                    ((vname_decl ::
                                                      tok_decl), env))
                                            in
                                         (match uu____8248 with
                                          | (decls2,env) ->
                                              let uu____8319 =
                                                let res_t =
                                                  FStar_Syntax_Subst.compress
                                                    res_t
                                                   in
                                                let uu____8324 =
                                                  encode_term res_t env'  in
                                                match uu____8324 with
                                                | (encoded_res_t,decls) ->
                                                    let _0_787 =
                                                      FStar_SMTEncoding_Term.mk_HasType
                                                        vapp encoded_res_t
                                                       in
                                                    (encoded_res_t, _0_787,
                                                      decls)
                                                 in
                                              (match uu____8319 with
                                               | (encoded_res_t,ty_pred,decls3)
                                                   ->
                                                   let typingAx =
                                                     FStar_SMTEncoding_Term.Assume
                                                       (let _0_789 =
                                                          FStar_SMTEncoding_Util.mkForall
                                                            (let _0_788 =
                                                               FStar_SMTEncoding_Util.mkImp
                                                                 (guard,
                                                                   ty_pred)
                                                                in
                                                             ([[vapp]], vars,
                                                               _0_788))
                                                           in
                                                        (_0_789,
                                                          (Some
                                                             "free var typing"),
                                                          (Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                vname))))
                                                      in
                                                   let freshness =
                                                     let uu____8348 =
                                                       FStar_All.pipe_right
                                                         quals
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.New)
                                                        in
                                                     match uu____8348 with
                                                     | true  ->
                                                         let _0_794 =
                                                           FStar_SMTEncoding_Term.fresh_constructor
                                                             (let _0_791 =
                                                                FStar_All.pipe_right
                                                                  vars
                                                                  (FStar_List.map
                                                                    Prims.snd)
                                                                 in
                                                              let _0_790 =
                                                                varops.next_id
                                                                  ()
                                                                 in
                                                              (vname, _0_791,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                _0_790))
                                                            in
                                                         let _0_793 =
                                                           let _0_792 =
                                                             pretype_axiom
                                                               vapp vars
                                                              in
                                                           [_0_792]  in
                                                         _0_794 :: _0_793
                                                     | uu____8356 -> []  in
                                                   let g =
                                                     let _0_799 =
                                                       let _0_798 =
                                                         let _0_797 =
                                                           let _0_796 =
                                                             let _0_795 =
                                                               mk_disc_proj_axioms
                                                                 guard
                                                                 encoded_res_t
                                                                 vapp vars
                                                                in
                                                             typingAx ::
                                                               _0_795
                                                              in
                                                           FStar_List.append
                                                             freshness _0_796
                                                            in
                                                         FStar_List.append
                                                           decls3 _0_797
                                                          in
                                                       FStar_List.append
                                                         decls2 _0_798
                                                        in
                                                     FStar_List.append decls1
                                                       _0_799
                                                      in
                                                   (g, env))))))))
  
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
          let uu____10599 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8379 with
          | None  ->
              let uu____8402 = encode_free_var env x t t_norm []  in
              (match uu____8402 with
               | (decls,env) ->
                   let uu____8417 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____8417 with
                    | (n,x',uu____8436) -> ((n, x'), decls, env)))
          | Some (n,x,uu____8448) -> ((n, x), [], env)
  
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
          let uu____8481 = encode_free_var env lid t tt quals  in
          match uu____8481 with
          | (decls,env) ->
              let uu____8492 = FStar_Syntax_Util.is_smt_lemma t  in
              (match uu____8492 with
               | true  ->
                   let _0_801 =
                     let _0_800 = encode_smt_lemma env lid tt  in
                     FStar_List.append decls _0_800  in
                   (_0_801, env)
               | uu____8497 -> (decls, env))
  
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
             (fun uu____10746  ->
                fun lb  ->
                  match uu____8522 with
                  | (decls,env) ->
                      let uu____8534 =
                        let _0_802 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env _0_802
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8534 with
                       | (decls',env) ->
                           ((FStar_List.append decls decls'), env)))
             ([], env))
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10835  ->
      fun quals  ->
        match uu____10835 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8610 = FStar_Util.first_N nbinders formals  in
              match uu____8610 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____8650  ->
                         fun uu____8651  ->
                           match (uu____8650, uu____8651) with
                           | ((formal,uu____8661),(binder,uu____8663)) ->
                               FStar_Syntax_Syntax.NT
                                 (let _0_803 =
                                    FStar_Syntax_Syntax.bv_to_name binder  in
                                  (formal, _0_803))) formals binders
                     in
                  let extra_formals =
                    let _0_806 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10966  ->
                              match uu____10966 with
                              | (x,i) ->
                                  let _0_805 =
                                    let uu___152_8695 = x  in
                                    let _0_804 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___155_10974.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___152_8695.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = _0_804
                                    }  in
                                  (_0_805, i)))
                       in
                    FStar_All.pipe_right _0_806
                      FStar_Syntax_Util.name_binders
                     in
                  let body =
                    let _0_812 =
                      let _0_811 =
                        (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
                         in
                      FStar_All.pipe_left (fun _0_810  -> Some _0_810) _0_811
                       in
                    (let _0_809 = FStar_Syntax_Subst.compress body  in
                     let _0_808 =
                       let _0_807 =
                         FStar_Syntax_Util.args_of_binders extra_formals  in
                       FStar_All.pipe_left Prims.snd _0_807  in
                     FStar_Syntax_Syntax.extend_app_n _0_809 _0_808) _0_812
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals), body)
               in
            let destruct_bound_function flid t_norm e =
              let rec aux norm t_norm =
                let uu____8756 = FStar_Syntax_Util.abs_formals e  in
                match uu____8756 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8809::uu____8810 ->
                         let uu____8818 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____8818 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8845 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8845 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = FStar_Syntax_Util.comp_result c
                                      in
                                   let uu____8875 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c)
                                      in
                                   (match uu____8875 with
                                    | true  ->
                                        let uu____8895 =
                                          FStar_Util.first_N nformals binders
                                           in
                                        (match uu____8895 with
                                         | (bs0,rest) ->
                                             let c =
                                               let subst =
                                                 FStar_List.map2
                                                   (fun uu____8943  ->
                                                      fun uu____8944  ->
                                                        match (uu____8943,
                                                                uu____8944)
                                                        with
                                                        | ((b,uu____8954),
                                                           (x,uu____8956)) ->
                                                            FStar_Syntax_Syntax.NT
                                                              (let _0_813 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   x
                                                                  in
                                                               (b, _0_813)))
                                                   bs0 formals
                                                  in
                                               FStar_Syntax_Subst.subst_comp
                                                 subst c
                                                in
                                             let body =
                                               FStar_Syntax_Util.abs rest
                                                 body lopt
                                                in
                                             ((bs0, body, bs0,
                                                (FStar_Syntax_Util.comp_result
                                                   c)), false))
                                    | uu____8982 ->
                                        (match nformals > nbinders with
                                         | true  ->
                                             let uu____9002 =
                                               eta_expand binders formals
                                                 body tres
                                                in
                                             (match uu____9002 with
                                              | (binders,body) ->
                                                  ((binders, body, formals,
                                                     tres), false))
                                         | uu____9054 ->
                                             ((binders, body, formals, tres),
                                               false))))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____9064) ->
                              let _0_814 =
                                Prims.fst
                                  (aux norm x.FStar_Syntax_Syntax.sort)
                                 in
                              (_0_814, true)
                          | uu____9093 when Prims.op_Negation norm ->
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
                                  env.tcenv t_norm
                                 in
                              aux true t_norm
                          | uu____9095 ->
                              failwith
                                (let _0_816 =
                                   FStar_Syntax_Print.term_to_string e  in
                                 let _0_815 =
                                   FStar_Syntax_Print.term_to_string t_norm
                                    in
                                 FStar_Util.format3
                                   "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                   flid.FStar_Ident.str _0_816 _0_815))
                     | uu____9110 ->
                         let uu____9111 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____9111 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____9138 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____9138 with
                               | (formals,c) ->
                                   let tres = FStar_Syntax_Util.comp_result c
                                      in
                                   let uu____9160 =
                                     eta_expand [] formals e tres  in
                                   (match uu____9160 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____9214 -> (([], e, [], t_norm), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11550 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp))
                  in
               match uu____9242 with
               | true  -> encode_top_level_vals env bindings quals
               | uu____9248 ->
                   let uu____9249 =
                     FStar_All.pipe_right bindings
                       (FStar_List.fold_left
                          (fun uu____9290  ->
                             fun lb  ->
                               match uu____9290 with
                               | (toks,typs,decls,env) ->
                                   ((let uu____9341 =
                                       FStar_Syntax_Util.is_lemma
                                         lb.FStar_Syntax_Syntax.lbtyp
                                        in
                                     match uu____9341 with
                                     | true  ->
                                         Prims.raise Let_rec_unencodeable
                                     | uu____9342 -> ());
                                    (let t_norm =
                                       whnf env lb.FStar_Syntax_Syntax.lbtyp
                                        in
                                     let uu____9344 =
                                       let _0_817 =
                                         FStar_Util.right
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       declare_top_level_let env _0_817
                                         lb.FStar_Syntax_Syntax.lbtyp t_norm
                                        in
                                     match uu____9344 with
                                     | (tok,decl,env) ->
                                         let _0_820 =
                                           let _0_819 =
                                             let _0_818 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             (_0_818, tok)  in
                                           _0_819 :: toks  in
                                         (_0_820, (t_norm :: typs), (decl ::
                                           decls), env)))) ([], [], [], env))
                      in
                   (match uu____9249 with
                    | (toks,typs,decls,env) ->
                        let toks = FStar_List.rev toks  in
                        let decls =
                          FStar_All.pipe_right (FStar_List.rev decls)
                            FStar_List.flatten
                           in
                        let typs = FStar_List.rev typs  in
                        let mk_app curry f ftok vars =
                          match vars with
                          | [] ->
                              FStar_SMTEncoding_Util.mkFreeV
                                (f, FStar_SMTEncoding_Term.Term_sort)
                          | uu____9477 ->
                              (match curry with
                               | true  ->
                                   (match ftok with
                                    | Some ftok -> mk_Apply ftok vars
                                    | None  ->
                                        let _0_821 =
                                          FStar_SMTEncoding_Util.mkFreeV
                                            (f,
                                              FStar_SMTEncoding_Term.Term_sort)
                                           in
                                        mk_Apply _0_821 vars)
                               | uu____9482 ->
                                   FStar_SMTEncoding_Util.mkApp
                                     (let _0_822 =
                                        FStar_List.map
                                          FStar_SMTEncoding_Util.mkFreeV vars
                                         in
                                      (f, _0_822)))
                           in
                        let uu____9486 =
                          (FStar_All.pipe_right quals
                             (FStar_Util.for_some
                                (fun uu___124_9488  ->
                                   match uu___124_9488 with
                                   | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                       true
                                   | uu____9489 -> false)))
                            ||
                            (FStar_All.pipe_right typs
                               (FStar_Util.for_some
                                  (fun t  ->
                                     let _0_823 =
                                       FStar_Syntax_Util.is_pure_or_ghost_function
                                         t
                                        in
                                     FStar_All.pipe_left Prims.op_Negation
                                       _0_823)))
                           in
                        (match uu____9486 with
                         | true  -> (decls, env)
                         | uu____9496 ->
                             (match Prims.op_Negation is_rec with
                              | true  ->
                                  (match (bindings, typs, toks) with
                                   | ({
                                        FStar_Syntax_Syntax.lbname =
                                          uu____9511;
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____9512;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____9513;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____9514;
                                        FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                                      (flid_fv,(f,ftok))::[]) ->
                                       let e = FStar_Syntax_Subst.compress e
                                          in
                                       let flid =
                                         (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       let uu____9556 =
                                         destruct_bound_function flid t_norm
                                           e
                                          in
                                       (match uu____9556 with
                                        | ((binders,body,uu____9568,uu____9569),curry)
                                            ->
                                            let uu____9575 =
                                              encode_binders None binders env
                                               in
                                            (match uu____9575 with
                                             | (vars,guards,env',binder_decls,uu____9591)
                                                 ->
                                                 let app =
                                                   mk_app curry f ftok vars
                                                    in
                                                 let uu____9599 =
                                                   let uu____9604 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Logic)
                                                      in
                                                   match uu____9604 with
                                                   | true  ->
                                                       let _0_825 =
                                                         FStar_SMTEncoding_Term.mk_Valid
                                                           app
                                                          in
                                                       let _0_824 =
                                                         encode_formula body
                                                           env'
                                                          in
                                                       (_0_825, _0_824)
                                                   | uu____9612 ->
                                                       let _0_826 =
                                                         encode_term body
                                                           env'
                                                          in
                                                       (app, _0_826)
                                                    in
                                                 (match uu____9599 with
                                                  | (app,(body,decls2)) ->
                                                      let eqn =
                                                        FStar_SMTEncoding_Term.Assume
                                                          (let _0_829 =
                                                             FStar_SMTEncoding_Util.mkForall
                                                               (let _0_827 =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    body)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  _0_827))
                                                              in
                                                           let _0_828 =
                                                             Some
                                                               (FStar_Util.format1
                                                                  "Equation for %s"
                                                                  flid.FStar_Ident.str)
                                                              in
                                                           (_0_829, _0_828,
                                                             (Some
                                                                (Prims.strcat
                                                                   "equation_"
                                                                   f))))
                                                         in
                                                      let _0_834 =
                                                        let _0_833 =
                                                          let _0_832 =
                                                            let _0_831 =
                                                              let _0_830 =
                                                                primitive_type_axioms
                                                                  env.tcenv
                                                                  flid f app
                                                                 in
                                                              FStar_List.append
                                                                [eqn] _0_830
                                                               in
                                                            FStar_List.append
                                                              decls2 _0_831
                                                             in
                                                          FStar_List.append
                                                            binder_decls
                                                            _0_832
                                                           in
                                                        FStar_List.append
                                                          decls _0_833
                                                         in
                                                      (_0_834, env))))
                                   | uu____9632 -> failwith "Impossible")
                              | uu____9647 ->
                                  let fuel =
                                    let _0_835 = varops.fresh "fuel"  in
                                    (_0_835,
                                      FStar_SMTEncoding_Term.Fuel_sort)
                                     in
                                  let fuel_tm =
                                    FStar_SMTEncoding_Util.mkFreeV fuel  in
                                  let env0 = env  in
                                  let uu____9653 =
                                    FStar_All.pipe_right toks
                                      (FStar_List.fold_left
                                         (fun uu____9692  ->
                                            fun uu____9693  ->
                                              match (uu____9692, uu____9693)
                                              with
                                              | ((gtoks,env),(flid_fv,
                                                              (f,ftok)))
                                                  ->
                                                  let flid =
                                                    (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                     in
                                                  let g =
                                                    varops.new_fvar
                                                      (FStar_Ident.lid_add_suffix
                                                         flid
                                                         "fuel_instrumented")
                                                     in
                                                  let gtok =
                                                    varops.new_fvar
                                                      (FStar_Ident.lid_add_suffix
                                                         flid
                                                         "fuel_instrumented_token")
                                                     in
                                                  let env =
                                                    let _0_838 =
                                                      let _0_837 =
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (g, [fuel_tm])
                                                         in
                                                      FStar_All.pipe_left
                                                        (fun _0_836  ->
                                                           Some _0_836)
                                                        _0_837
                                                       in
                                                    push_free_var env flid
                                                      gtok _0_838
                                                     in
                                                  (((flid, f, ftok, g, gtok)
                                                    :: gtoks), env))
                                         ([], env))
                                     in
                                  (match uu____9653 with
                                   | (gtoks,env) ->
                                       let gtoks = FStar_List.rev gtoks  in
                                       let encode_one_binding env0 uu____9860
                                         t_norm uu____9862 =
                                         match (uu____9860, uu____9862) with
                                         | ((flid,f,ftok,g,gtok),{
                                                                   FStar_Syntax_Syntax.lbname
                                                                    = lbn;
                                                                   FStar_Syntax_Syntax.lbunivs
                                                                    =
                                                                    uu____9886;
                                                                   FStar_Syntax_Syntax.lbtyp
                                                                    =
                                                                    uu____9887;
                                                                   FStar_Syntax_Syntax.lbeff
                                                                    =
                                                                    uu____9888;
                                                                   FStar_Syntax_Syntax.lbdef
                                                                    = e;_})
                                             ->
                                             ((let uu____9906 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env0.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               match uu____9906 with
                                               | true  ->
                                                   let _0_841 =
                                                     FStar_Syntax_Print.lbname_to_string
                                                       lbn
                                                      in
                                                   let _0_840 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t_norm
                                                      in
                                                   let _0_839 =
                                                     FStar_Syntax_Print.term_to_string
                                                       e
                                                      in
                                                   FStar_Util.print3
                                                     "Encoding let rec %s : %s = %s\n"
                                                     _0_841 _0_840 _0_839
                                               | uu____9907 -> ());
                                              (let uu____9908 =
                                                 destruct_bound_function flid
                                                   t_norm e
                                                  in
                                               match uu____9908 with
                                               | ((binders,body,formals,tres),curry)
                                                   ->
                                                   ((let uu____9930 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env0.tcenv)
                                                         (FStar_Options.Other
                                                            "SMTEncoding")
                                                        in
                                                     match uu____9930 with
                                                     | true  ->
                                                         let _0_843 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", " binders
                                                            in
                                                         let _0_842 =
                                                           FStar_Syntax_Print.term_to_string
                                                             body
                                                            in
                                                         FStar_Util.print2
                                                           "Encoding let rec: binders=[%s], body=%s\n"
                                                           _0_843 _0_842
                                                     | uu____9931 -> ());
                                                    (match curry with
                                                     | true  ->
                                                         failwith
                                                           "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                     | uu____9933 -> ());
                                                    (let uu____9934 =
                                                       encode_binders None
                                                         binders env
                                                        in
                                                     match uu____9934 with
                                                     | (vars,guards,env',binder_decls,uu____9952)
                                                         ->
                                                         let decl_g =
                                                           FStar_SMTEncoding_Term.DeclFun
                                                             (let _0_845 =
                                                                let _0_844 =
                                                                  FStar_List.map
                                                                    Prims.snd
                                                                    vars
                                                                   in
                                                                FStar_SMTEncoding_Term.Fuel_sort
                                                                  :: _0_844
                                                                 in
                                                              (g, _0_845,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                (Some
                                                                   "Fuel-instrumented function name")))
                                                            in
                                                         let env0 =
                                                           push_zfuel_name
                                                             env0 flid g
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
                                                           FStar_SMTEncoding_Util.mkApp
                                                             (let _0_846 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars
                                                                 in
                                                              (f, _0_846))
                                                            in
                                                         let gsapp =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             (let _0_848 =
                                                                let _0_847 =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                   in
                                                                _0_847 ::
                                                                  vars_tm
                                                                 in
                                                              (g, _0_848))
                                                            in
                                                         let gmax =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             (let _0_850 =
                                                                let _0_849 =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])
                                                                   in
                                                                _0_849 ::
                                                                  vars_tm
                                                                 in
                                                              (g, _0_850))
                                                            in
                                                         let uu____9982 =
                                                           encode_term body
                                                             env'
                                                            in
                                                         (match uu____9982
                                                          with
                                                          | (body_tm,decls2)
                                                              ->
                                                              let eqn_g =
                                                                FStar_SMTEncoding_Term.Assume
                                                                  (let _0_853
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall'
                                                                    (let _0_851
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_851))
                                                                     in
                                                                   let _0_852
                                                                    =
                                                                    Some
                                                                    (FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str)
                                                                     in
                                                                   (_0_853,
                                                                    _0_852,
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))))
                                                                 in
                                                              let eqn_f =
                                                                FStar_SMTEncoding_Term.Assume
                                                                  (let _0_855
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_854
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_854))
                                                                     in
                                                                   (_0_855,
                                                                    (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))))
                                                                 in
                                                              let eqn_g' =
                                                                FStar_SMTEncoding_Term.Assume
                                                                  (let _0_860
                                                                    =
                                                                    let uu____12509
                                                                    =
                                                                    let uu____12512
                                                                    =
                                                                    let uu____12513
                                                                    =
                                                                    let uu____12517
                                                                    =
                                                                    let uu____12519
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    _0_856 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_857))
                                                                     in
                                                                    (gsapp,
                                                                    _0_858))
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_859))
                                                                     in
                                                                   (_0_860,
                                                                    (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))))
                                                                 in
                                                              let uu____10026
                                                                =
                                                                let uu____10031
                                                                  =
                                                                  encode_binders
                                                                    None
                                                                    formals
                                                                    env0
                                                                   in
                                                                match uu____10031
                                                                with
                                                                | (vars,v_guards,env,binder_decls,uu____10048)
                                                                    ->
                                                                    let vars_tm
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    let gapp
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm))
                                                                     in
                                                                    let tok_corr
                                                                    =
                                                                    let tok_app
                                                                    =
                                                                    let uu____12568
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12568
                                                                    (fuel ::
                                                                    vars)  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_863
                                                                    =
                                                                    let uu____12575
                                                                    =
                                                                    let uu____12576
                                                                    =
                                                                    let uu____12582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_862))
                                                                     in
                                                                    (_0_863,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))))
                                                                     in
                                                                    let uu____10076
                                                                    =
                                                                    let uu____10080
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env gapp
                                                                     in
                                                                    match uu____10080
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12607
                                                                    =
                                                                    let uu____12608
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    let uu____12613
                                                                    =
                                                                    let uu____12619
                                                                    =
                                                                    let uu____12620
                                                                    =
                                                                    let uu____12623
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (_0_864,
                                                                    g_typing))
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_865))
                                                                     in
                                                                    (_0_866,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))))  in
                                                                    [_0_867]
                                                                     in
                                                                    (d3,
                                                                    _0_868)
                                                                     in
                                                                    (match uu____10076
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                                 in
                                                              (match uu____10026
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
                                                                    env0)))))))
                                          in
                                       let uu____10123 =
                                         let _0_869 =
                                           FStar_List.zip3 gtoks typs
                                             bindings
                                            in
                                         FStar_List.fold_left
                                           (fun uu____10145  ->
                                              fun uu____10146  ->
                                                match (uu____10145,
                                                        uu____10146)
                                                with
                                                | ((decls,eqns,env0),
                                                   (gtok,ty,lb)) ->
                                                    let uu____10222 =
                                                      encode_one_binding env0
                                                        gtok ty lb
                                                       in
                                                    (match uu____10222 with
                                                     | (decls',eqns',env0) ->
                                                         ((decls' :: decls),
                                                           (FStar_List.append
                                                              eqns' eqns),
                                                           env0)))
                                           ([decls], [], env0) _0_869
                                          in
                                       (match uu____10123 with
                                        | (decls,eqns,env0) ->
                                            let uu____10268 =
                                              let _0_870 =
                                                FStar_All.pipe_right decls
                                                  FStar_List.flatten
                                                 in
                                              FStar_All.pipe_right _0_870
                                                (FStar_List.partition
                                                   (fun uu___125_10281  ->
                                                      match uu___125_10281
                                                      with
                                                      | FStar_SMTEncoding_Term.DeclFun
                                                          uu____10282 -> true
                                                      | uu____10288 -> false))
                                               in
                                            (match uu____10268 with
                                             | (prefix_decls,rest) ->
                                                 let eqns =
                                                   FStar_List.rev eqns  in
                                                 ((FStar_List.append
                                                     prefix_decls
                                                     (FStar_List.append rest
                                                        eqns)), env0)))))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12857 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right _0_871 (FStar_String.concat " and ")
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
      (let uu____12890 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       match uu____10337 with
       | true  ->
           let _0_872 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
             _0_872
       | uu____10338 -> ());
      (let nm =
         let uu____10340 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____10340 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____10343 = encode_sigelt' env se  in
       match uu____10343 with
       | (g,e) ->
           (match g with
            | [] ->
                let _0_874 =
                  let _0_873 =
                    FStar_SMTEncoding_Term.Caption
                      (FStar_Util.format1 "<Skipped %s/>" nm)
                     in
                  [_0_873]  in
                (_0_874, e)
            | uu____10353 ->
                let _0_879 =
                  let _0_878 =
                    let _0_875 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "<Start encoding %s>" nm)
                       in
                    _0_875 :: g  in
                  let _0_877 =
                    let _0_876 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "</end encoding %s>" nm)
                       in
                    [_0_876]  in
                  FStar_List.append _0_878 _0_877  in
                (_0_879, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12929 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12938 =
            let uu____12939 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right _0_880 Prims.op_Negation  in
          (match uu____10373 with
           | true  -> ([], env)
           | uu____10378 ->
               let close_effect_params tm =
                 match ed.FStar_Syntax_Syntax.binders with
                 | [] -> tm
                 | uu____10393 ->
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (let _0_882 =
                              FStar_All.pipe_left
                                (fun _0_881  -> Some _0_881)
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))
                               in
                            ((ed.FStar_Syntax_Syntax.binders), tm, _0_882))))
                       None tm.FStar_Syntax_Syntax.pos
                  in
               let encode_action env a =
                 let uu____10440 =
                   new_term_constant_and_tok_from_lid env
                     a.FStar_Syntax_Syntax.action_name
                    in
                 match uu____10440 with
                 | (aname,atok,env) ->
                     let uu____10450 =
                       FStar_Syntax_Util.arrow_formals_comp
                         a.FStar_Syntax_Syntax.action_typ
                        in
                     (match uu____10450 with
                      | (formals,uu____10460) ->
                          let uu____10467 =
                            let _0_883 =
                              close_effect_params
                                a.FStar_Syntax_Syntax.action_defn
                               in
                            encode_term _0_883 env  in
                          (match uu____10467 with
                           | (tm,decls) ->
                               let a_decls =
                                 let _0_885 =
                                   FStar_SMTEncoding_Term.DeclFun
                                     (let _0_884 =
                                        FStar_All.pipe_right formals
                                          (FStar_List.map
                                             (fun uu____10485  ->
                                                FStar_SMTEncoding_Term.Term_sort))
                                         in
                                      (aname, _0_884,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        (Some "Action")))
                                    in
                                 [_0_885;
                                 FStar_SMTEncoding_Term.DeclFun
                                   (atok, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action token"))]
                                  in
                               let uu____10490 =
                                 let _0_886 =
                                   FStar_All.pipe_right formals
                                     (FStar_List.map
                                        (fun uu____10522  ->
                                           match uu____10522 with
                                           | (bv,uu____10530) ->
                                               let uu____10531 =
                                                 gen_term_var env bv  in
                                               (match uu____10531 with
                                                | (xxsym,xx,uu____10541) ->
                                                    ((xxsym,
                                                       FStar_SMTEncoding_Term.Term_sort),
                                                      xx))))
                                    in
                                 FStar_All.pipe_right _0_886 FStar_List.split
                                  in
                               (match uu____10490 with
                                | (xs_sorts,xs) ->
                                    let app =
                                      FStar_SMTEncoding_Util.mkApp
                                        (let _0_888 =
                                           let _0_887 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (aname, xs)
                                              in
                                           [_0_887]  in
                                         ("Reify", _0_888))
                                       in
                                    let a_eq =
                                      FStar_SMTEncoding_Term.Assume
                                        (let _0_891 =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_890 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (let _0_889 =
                                                     mk_Apply tm xs_sorts  in
                                                   (app, _0_889))
                                                 in
                                              ([[app]], xs_sorts, _0_890))
                                            in
                                         (_0_891, (Some "Action equality"),
                                           (Some
                                              (Prims.strcat aname "_equality"))))
                                       in
                                    let tok_correspondence =
                                      let tok_term =
                                        FStar_SMTEncoding_Util.mkFreeV
                                          (atok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         in
                                      let tok_app =
                                        mk_Apply tok_term xs_sorts  in
                                      FStar_SMTEncoding_Term.Assume
                                        (let _0_893 =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_892 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (tok_app, app)
                                                 in
                                              ([[tok_app]], xs_sorts, _0_892))
                                            in
                                         (_0_893,
                                           (Some
                                              "Action token correspondence"),
                                           (Some
                                              (Prims.strcat aname
                                                 "_token_correspondence"))))
                                       in
                                    (env,
                                      (FStar_List.append decls
                                         (FStar_List.append a_decls
                                            [a_eq; tok_correspondence]))))))
                  in
               let uu____10585 =
                 FStar_Util.fold_map encode_action env
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____10585 with
                | (env,decls2) -> ((FStar_List.flatten decls2), env)))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____13286,uu____13287,uu____13288) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____10607 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____10607 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10618,t,quals,uu____10621) ->
          let will_encode_definition =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___126_10626  ->
                       match uu___126_10626 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _
                           |FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____10629 -> false)))
             in
          (match will_encode_definition with
           | true  -> ([], env)
           | uu____10633 ->
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_constant None
                  in
               let uu____10635 = encode_top_level_val env fv t quals  in
               (match uu____10635 with
                | (decls,env) ->
                    let tname = lid.FStar_Ident.str  in
                    let tsym =
                      FStar_SMTEncoding_Util.mkFreeV
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    let _0_895 =
                      let _0_894 =
                        primitive_type_axioms env.tcenv lid tname tsym  in
                      FStar_List.append decls _0_894  in
                    (_0_895, env)))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____10650,uu____10651) ->
          let uu____10654 = encode_formula f env  in
          (match uu____10654 with
           | (f,decls) ->
               let g =
                 let _0_899 =
                   FStar_SMTEncoding_Term.Assume
                     (let _0_898 =
                        Some
                          (let _0_896 = FStar_Syntax_Print.lid_to_string l
                              in
                           FStar_Util.format1 "Assumption: %s" _0_896)
                         in
                      let _0_897 =
                        Some
                          (varops.mk_unique
                             (Prims.strcat "assumption_" l.FStar_Ident.str))
                         in
                      (f, _0_898, _0_897))
                    in
                 [_0_899]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13363,quals,uu____13365) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13373 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let uu____10689 =
                     let _0_900 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone _0_900  in
                   match uu____10689 with
                   | true  ->
                       let val_decl =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp), quals, r)
                          in
                       let uu____10704 = encode_sigelt' env val_decl  in
                       (match uu____10704 with | (decls,env) -> (env, decls))
                   | uu____10711 -> (env, [])) env (Prims.snd lbs)
             in
          (match uu____10678 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13426,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13428;
                          FStar_Syntax_Syntax.lbtyp = uu____13429;
                          FStar_Syntax_Syntax.lbeff = uu____13430;
                          FStar_Syntax_Syntax.lbdef = uu____13431;_}::[]),uu____13432,uu____13433,uu____13434)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13450 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10746 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp
                   (let _0_902 =
                      let _0_901 =
                        FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                      [_0_901]  in
                    ("Valid", _0_902))
                  in
               let decls =
                 let _0_907 =
                   let _0_906 =
                     FStar_SMTEncoding_Term.Assume
                       (let _0_905 =
                          FStar_SMTEncoding_Util.mkForall
                            (let _0_904 =
                               FStar_SMTEncoding_Util.mkEq
                                 (let _0_903 =
                                    FStar_SMTEncoding_Util.mkApp
                                      ("BoxBool_proj_0", [x])
                                     in
                                  (valid_b2t_x, _0_903))
                                in
                             ([[valid_b2t_x]], [xx], _0_904))
                           in
                        (_0_905, (Some "b2t def"), (Some "b2t_def")))
                      in
                   [_0_906]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: _0_907
                  in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____13514,uu____13515,quals,uu____13517) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_13525  ->
                  match uu___128_13525 with
                  | FStar_Syntax_Syntax.Discriminator uu____13526 -> true
                  | uu____13527 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13529,lids,quals,uu____13532) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let _0_908 =
                     (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText  in
                   _0_908 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_13544  ->
                     match uu___129_13544 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13545 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____13548,quals,uu____13550) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_13562  ->
                  match uu___130_13562 with
                  | FStar_Syntax_Syntax.Projector uu____13563 -> true
                  | uu____13566 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10845 = try_lookup_free_var env l  in
          (match uu____10845 with
           | Some uu____10849 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l))
                  in
               encode_sigelt env se)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____10857,uu____10858,quals,uu____10860) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let uu____10872 =
            (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
             in
          (match uu____10872 with
           | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10877) ->
               let body = FStar_Syntax_Util.mk_reify body  in
               let tm =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_abs (bs, body, None))) None
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
                 let uu____10934 =
                   FStar_Syntax_Util.arrow_formals_comp
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 match uu____10934 with
                 | (formals,comp) ->
                     let reified_typ =
                       FStar_TypeChecker_Util.reify_comp
                         (let uu___155_10951 = env.tcenv  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___155_10951.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___155_10951.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___155_10951.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___155_10951.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___155_10951.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___155_10951.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___155_10951.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___155_10951.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___155_10951.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___155_10951.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___155_10951.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___155_10951.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___155_10951.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___155_10951.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___155_10951.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___155_10951.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___155_10951.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___155_10951.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___155_10951.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___155_10951.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___155_10951.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___155_10951.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___155_10951.FStar_TypeChecker_Env.qname_and_index)
                          }) (FStar_Syntax_Util.lcomp_of_comp comp)
                         FStar_Syntax_Syntax.U_unknown
                        in
                     let _0_909 = FStar_Syntax_Syntax.mk_Total reified_typ
                        in
                     FStar_Syntax_Util.arrow formals _0_909
                  in
               let lb =
                 let uu___156_10953 = lb  in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___156_10953.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___156_10953.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = lb_typ;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___156_10953.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef = tm'
                 }  in
               encode_top_level_let env (false, [lb]) quals
           | uu____10955 -> ([], env))
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13586,quals,uu____13588) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____10976,uu____10977,uu____10978) ->
          let uu____10985 = encode_signature env ses  in
          (match uu____10985 with
           | (g,env) ->
               let uu____10995 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_13630  ->
                         match uu___131_13630 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____13631,Some "inversion axiom",uu____13632)
                             -> false
                         | uu____11011 -> true))
                  in
               (match uu____10995 with
                | (g',inversions) ->
                    let uu____13643 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_13653  ->
                              match uu___132_13653 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13654 ->
                                  true
                              | uu____11037 -> false))
                       in
                    (match uu____11020 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13671,tps,k,uu____13674,datas,quals) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_13685  ->
                    match uu___133_13685 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11064 -> false))
             in
          let constructor_or_logic_type_decl c =
            match is_logical with
            | true  ->
                let uu____11071 = c  in
                (match uu____11071 with
                 | (name,args,uu____11075,uu____11076,uu____11077) ->
                     let _0_911 =
                       FStar_SMTEncoding_Term.DeclFun
                         (let _0_910 =
                            FStar_All.pipe_right args
                              (FStar_List.map
                                 (fun uu____11087  ->
                                    match uu____11087 with
                                    | (uu____11091,sort,uu____11093) -> sort))
                             in
                          (name, _0_910, FStar_SMTEncoding_Term.Term_sort,
                            None))
                        in
                     [_0_911])
            | uu____11094 -> FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13740 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let _0_912 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right _0_912 FStar_Option.isNone))
               in
            match uu____11109 with
            | true  -> []
            | uu____11118 ->
                let uu____11119 =
                  fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
                (match uu____11119 with
                 | (xxsym,xx) ->
                     let uu____11125 =
                       FStar_All.pipe_right datas
                         (FStar_List.fold_left
                            (fun uu____11136  ->
                               fun l  ->
                                 match uu____11136 with
                                 | (out,decls) ->
                                     let uu____11148 =
                                       FStar_TypeChecker_Env.lookup_datacon
                                         env.tcenv l
                                        in
                                     (match uu____11148 with
                                      | (uu____11154,data_t) ->
                                          let uu____11156 =
                                            FStar_Syntax_Util.arrow_formals
                                              data_t
                                             in
                                          (match uu____11156 with
                                           | (args,res) ->
                                               let indices =
                                                 let uu____11185 =
                                                   (FStar_Syntax_Subst.compress
                                                      res).FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____11185 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____11191,indices) ->
                                                     indices
                                                 | uu____11207 -> []  in
                                               let env =
                                                 FStar_All.pipe_right args
                                                   (FStar_List.fold_left
                                                      (fun env  ->
                                                         fun uu____11219  ->
                                                           match uu____11219
                                                           with
                                                           | (x,uu____11223)
                                                               ->
                                                               let _0_914 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   (let _0_913
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x  in
                                                                    (_0_913,
                                                                    [xx]))
                                                                  in
                                                               push_term_var
                                                                 env x _0_914)
                                                      env)
                                                  in
                                               let uu____11225 =
                                                 encode_args indices env  in
                                               (match uu____11225 with
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
                                                      | uu____11243 -> ());
                                                     (let eqs =
                                                        let _0_916 =
                                                          FStar_List.map2
                                                            (fun v  ->
                                                               fun a  ->
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   (let _0_915
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    (_0_915,
                                                                    a))) vars
                                                            indices
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_916
                                                          FStar_SMTEncoding_Util.mk_and_l
                                                         in
                                                      let _0_919 =
                                                        FStar_SMTEncoding_Util.mkOr
                                                          (let _0_918 =
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               (let _0_917 =
                                                                  mk_data_tester
                                                                    env l xx
                                                                   in
                                                                (_0_917, eqs))
                                                              in
                                                           (out, _0_918))
                                                         in
                                                      (_0_919,
                                                        (FStar_List.append
                                                           decls decls'))))))))
                            (FStar_SMTEncoding_Util.mkFalse, []))
                        in
                     (match uu____11125 with
                      | (data_ax,decls) ->
                          let uu____11259 =
                            fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                             in
                          (match uu____11259 with
                           | (ffsym,ff) ->
                               let fuel_guarded_inversion =
                                 let xx_has_type_sfuel =
                                   match (FStar_List.length datas) >
                                           (Prims.parse_int "1")
                                   with
                                   | true  ->
                                       let _0_920 =
                                         FStar_SMTEncoding_Util.mkApp
                                           ("SFuel", [ff])
                                          in
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         _0_920 xx tapp
                                   | uu____11271 ->
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp
                                    in
                                 FStar_SMTEncoding_Term.Assume
                                   (let _0_924 =
                                      FStar_SMTEncoding_Util.mkForall
                                        (let _0_922 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let _0_921 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_sfuel, data_ax)
                                            in
                                         ([[xx_has_type_sfuel]], _0_922,
                                           _0_921))
                                       in
                                    let _0_923 =
                                      Some
                                        (varops.mk_unique
                                           (Prims.strcat
                                              "fuel_guarded_inversion_"
                                              t.FStar_Ident.str))
                                       in
                                    (_0_924, (Some "inversion axiom"),
                                      _0_923))
                                  in
                               let pattern_guarded_inversion =
                                 let uu____11287 =
                                   (contains_name env "Prims.inversion") &&
                                     ((FStar_List.length datas) >
                                        (Prims.parse_int "1"))
                                    in
                                 match uu____11287 with
                                 | true  ->
                                     let xx_has_type_fuel =
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp
                                        in
                                     let pattern_guard =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("Prims.inversion", [tapp])
                                        in
                                     let _0_929 =
                                       FStar_SMTEncoding_Term.Assume
                                         (let _0_928 =
                                            FStar_SMTEncoding_Util.mkForall
                                              (let _0_926 =
                                                 add_fuel
                                                   (ffsym,
                                                     FStar_SMTEncoding_Term.Fuel_sort)
                                                   ((xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   :: vars)
                                                  in
                                               let _0_925 =
                                                 FStar_SMTEncoding_Util.mkImp
                                                   (xx_has_type_fuel,
                                                     data_ax)
                                                  in
                                               ([[xx_has_type_fuel;
                                                 pattern_guard]], _0_926,
                                                 _0_925))
                                             in
                                          let _0_927 =
                                            Some
                                              (varops.mk_unique
                                                 (Prims.strcat
                                                    "pattern_guarded_inversion_"
                                                    t.FStar_Ident.str))
                                             in
                                          (_0_928, (Some "inversion axiom"),
                                            _0_927))
                                        in
                                     [_0_929]
                                 | uu____11308 -> []  in
                               FStar_List.append decls
                                 (FStar_List.append [fuel_guarded_inversion]
                                    pattern_guarded_inversion))))
             in
          let uu____11309 =
            let uu____11317 =
              (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n  in
            match uu____11317 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____11344 -> (tps, k)  in
          (match uu____11309 with
           | (formals,res) ->
               let uu____11359 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11359 with
                | (formals,res) ->
                    let uu____11366 = encode_binders None formals env  in
                    (match uu____11366 with
                     | (vars,guards,env',binder_decls,uu____11381) ->
                         let uu____11388 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____11388 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (let _0_930 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, _0_930))
                                 in
                              let uu____11404 =
                                let tname_decl =
                                  constructor_or_logic_type_decl
                                    (let _0_932 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun uu____11424  ->
                                               match uu____11424 with
                                               | (n,s) ->
                                                   ((Prims.strcat tname n),
                                                     s, false)))
                                        in
                                     let _0_931 = varops.next_id ()  in
                                     (tname, _0_932,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       _0_931, false))
                                   in
                                let uu____11432 =
                                  match vars with
                                  | [] ->
                                      let uu____14154 =
                                        let uu____14155 =
                                          let uu____14157 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_933  -> Some _0_933)
                                            _0_934
                                           in
                                        push_free_var env t tname _0_935  in
                                      ([], _0_936)
                                  | uu____11442 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let _0_937 = varops.next_id ()  in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          _0_937
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14176 =
                                          let uu____14180 =
                                            let uu____14181 =
                                              let uu____14189 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14189) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14181 in
                                          (uu____14180,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Term.Assume
                                          (let _0_939 =
                                             FStar_SMTEncoding_Util.mkForall'
                                               (let _0_938 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats, None, vars, _0_938))
                                              in
                                           (_0_939,
                                             (Some
                                                "name-token correspondence"),
                                             (Some
                                                (Prims.strcat
                                                   "token_correspondence_"
                                                   ttok))))
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env)
                                   in
                                match uu____11432 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env)
                                 in
                              (match uu____11404 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____11479 =
                                       encode_term_pred None res env' tapp
                                        in
                                     match uu____11479 with
                                     | (k,decls) ->
                                         let karr =
                                           match (FStar_List.length formals)
                                                   > (Prims.parse_int "0")
                                           with
                                           | true  ->
                                               let _0_942 =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_941 =
                                                      let _0_940 =
                                                        FStar_SMTEncoding_Term.mk_PreType
                                                          ttok_tm
                                                         in
                                                      FStar_SMTEncoding_Term.mk_tester
                                                        "Tm_arrow" _0_940
                                                       in
                                                    (_0_941,
                                                      (Some "kinding"),
                                                      (Some
                                                         (Prims.strcat
                                                            "pre_kinding_"
                                                            ttok))))
                                                  in
                                               [_0_942]
                                           | uu____11495 -> []  in
                                         let _0_947 =
                                           let _0_946 =
                                             let _0_945 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_944 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      (let _0_943 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k)
                                                          in
                                                       ([[tapp]], vars,
                                                         _0_943))
                                                     in
                                                  (_0_944, None,
                                                    (Some
                                                       (Prims.strcat
                                                          "kinding_" ttok))))
                                                in
                                             [_0_945]  in
                                           FStar_List.append karr _0_946  in
                                         FStar_List.append decls _0_947
                                      in
                                   let aux =
                                     let _0_951 =
                                       let _0_950 =
                                         inversion_axioms tapp vars  in
                                       let _0_949 =
                                         let _0_948 = pretype_axiom tapp vars
                                            in
                                         [_0_948]  in
                                       FStar_List.append _0_950 _0_949  in
                                     FStar_List.append kindingAx _0_951  in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14271,uu____14272,uu____14273,uu____14274,uu____14275,uu____14276)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11522,t,uu____11524,n_tps,quals,uu____11527,drange) ->
          let uu____11533 = new_term_constant_and_tok_from_lid env d  in
          (match uu____11533 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____11544 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____11544 with
                | (formals,t_res) ->
                    let uu____11566 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____11566 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11575 =
                           encode_binders (Some fuel_tm) formals env  in
                         (match uu____11575 with
                          | (vars,guards,env',binder_decls,names) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let _0_952 =
                                            mk_term_projector_name d x  in
                                          (_0_952,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let _0_954 =
                                  let _0_953 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort, _0_953,
                                    true)
                                   in
                                FStar_All.pipe_right _0_954
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
                              let uu____11635 =
                                encode_term_pred None t env ddtok_tm  in
                              (match uu____11635 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14415::uu____14416 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____14441 =
                                           let uu____14447 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14447) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14441
                                     | uu____14460 -> tok_typing in
                                   let uu____14465 =
                                     encode_binders (Some fuel_tm) formals
                                       env
                                      in
                                   (match uu____11642 with
                                    | (vars',guards',env'',decls_formals,uu____11657)
                                        ->
                                        let uu____14487 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars)
                                             in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp
                                           in
                                        (match uu____11664 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11683 ->
                                                   let _0_956 =
                                                     let _0_955 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       _0_955
                                                      in
                                                   [_0_956]
                                                in
                                             let encode_elim uu____11693 =
                                               let uu____11694 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11694 with
                                               | (head,args) ->
                                                   let uu____11723 =
                                                     (FStar_Syntax_Subst.compress
                                                        head).FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11723 with
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
                                                        let uu____11739 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____11739
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
                                                                 | uu____14593
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable"
                                                                  in
                                                               let guards =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14601
                                                                    =
                                                                    let uu____14602
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv _0_957
                                                                     in
                                                                    match uu____11773
                                                                    with
                                                                    | 
                                                                    true  ->
                                                                    let _0_958
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv xv
                                                                     in
                                                                    [_0_958]
                                                                    | 
                                                                    uu____11777
                                                                    -> []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards
                                                                in
                                                             let uu____11778
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14624
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14624
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14646
                                                                    =
                                                                    let uu____14650
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env
                                                                    _0_959
                                                                     in
                                                                    (match uu____11813
                                                                    with
                                                                    | 
                                                                    (uu____14657,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14663
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    _0_960 ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14665
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    _0_961 ::
                                                                    eqns_or_guards
                                                                     in
                                                                    (env, (xv
                                                                    ::
                                                                    eqns_or_guards) in
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
                                                             (match uu____11778
                                                              with
                                                              | (uu____14673,arg_vars,elim_eqns_or_guards,uu____14676)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars)
                                                                     in
                                                                  let xvars =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14695
                                                                    =
                                                                    let uu____14699
                                                                    =
                                                                    let uu____14700
                                                                    =
                                                                    let uu____14706
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_963
                                                                    =
                                                                    let uu____14713
                                                                    =
                                                                    let uu____14716
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    _0_962))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_964,
                                                                    _0_963))
                                                                     in
                                                                    (_0_965,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))))
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14729
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (_0_966,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_974
                                                                    =
                                                                    let uu____14735
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    let uu____14747
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    [_0_967]
                                                                     in
                                                                    [_0_968]
                                                                     in
                                                                    let _0_971
                                                                    =
                                                                    let uu____14751
                                                                    =
                                                                    let uu____14754
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let _0_969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    (_0_970,
                                                                    _0_969))
                                                                     in
                                                                    (_0_972,
                                                                    [x],
                                                                    _0_971))
                                                                     in
                                                                    let _0_973
                                                                    =
                                                                    Some
                                                                    (varops.mk_unique
                                                                    "lextop")
                                                                     in
                                                                    (_0_974,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14765) in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    uu____14731
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14770
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
                                                                    (let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    _0_975
                                                                    dapp  in
                                                                    [_0_976]))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    _0_977
                                                                    FStar_List.flatten
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_981
                                                                    =
                                                                    let uu____14794
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_979
                                                                    =
                                                                    let uu____14808
                                                                    =
                                                                    let uu____14811
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    _0_978))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_980,
                                                                    _0_979))
                                                                     in
                                                                    (_0_981,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))))
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14821 ->
                                                        ((let uu____14823 =
                                                            let uu____14824 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let _0_982 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              _0_983 _0_982
                                                             in
                                                          FStar_Errors.warn
                                                            drange _0_984);
                                                         ([], [])))
                                                in
                                             let uu____11922 = encode_elim ()
                                                in
                                             (match uu____11922 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14840 =
                                                      let uu____14842 =
                                                        let uu____14844 =
                                                          let uu____14846 =
                                                            let uu____14848 =
                                                              let uu____14849
                                                                =
                                                                let uu____14855
                                                                  =
                                                                  let uu____14857
                                                                    =
                                                                    let uu____14858
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    _0_985)
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   _0_986))
                                                               in
                                                            [_0_987]  in
                                                          let _0_1001 =
                                                            let _0_1000 =
                                                              let _0_999 =
                                                                let _0_998 =
                                                                  let _0_997
                                                                    =
                                                                    let uu____14871
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14874
                                                                    =
                                                                    let uu____14878
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_988))
                                                                     in
                                                                    (_0_989,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))))
                                                                     in
                                                                    let _0_994
                                                                    =
                                                                    let uu____14894
                                                                    =
                                                                    let uu____14895
                                                                    =
                                                                    let uu____14899
                                                                    =
                                                                    let uu____14900
                                                                    =
                                                                    let uu____14906
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let _0_990
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    _0_991,
                                                                    _0_990))
                                                                     in
                                                                    (_0_992,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))))
                                                                     in
                                                                    [_0_993]
                                                                     in
                                                                    _0_995 ::
                                                                    _0_994
                                                                     in
                                                                    (FStar_SMTEncoding_Term.Assume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok))))
                                                                    :: _0_996
                                                                     in
                                                                  FStar_List.append
                                                                    _0_997
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  _0_998
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                _0_999
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              _0_1000
                                                             in
                                                          FStar_List.append
                                                            _0_1002 _0_1001
                                                           in
                                                        FStar_List.append
                                                          decls3 _0_1003
                                                         in
                                                      FStar_List.append
                                                        decls2 _0_1004
                                                       in
                                                    FStar_List.append
                                                      binder_decls _0_1005
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env)))))))))

and encode_signature :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14933  ->
              fun se  ->
                match uu____11967 with
                | (g,env) ->
                    let uu____11979 = encode_sigelt env se  in
                    (match uu____11979 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14981 =
        match uu____14981 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14999 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____12038 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   match uu____12038 with
                   | true  ->
                       let _0_1008 = FStar_Syntax_Print.bv_to_string x  in
                       let _0_1007 =
                         FStar_Syntax_Print.term_to_string
                           x.FStar_Syntax_Syntax.sort
                          in
                       let _0_1006 = FStar_Syntax_Print.term_to_string t1  in
                       FStar_Util.print3 "Normalized %s : %s to %s\n" _0_1008
                         _0_1007 _0_1006
                   | uu____12039 -> ());
                  (let uu____12040 = encode_term t1 env  in
                   match uu____12040 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12050 =
                         let _0_1013 =
                           let _0_1012 =
                             let _0_1011 = FStar_Util.digest_of_string t_hash
                                in
                             let _0_1010 =
                               let _0_1009 = FStar_Util.string_of_int i  in
                               Prims.strcat "_" _0_1009  in
                             Prims.strcat _0_1011 _0_1010  in
                           Prims.strcat "x_" _0_1012  in
                         new_term_constant_from_string env x _0_1013  in
                       (match uu____12050 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____12064 = FStar_Options.log_queries ()
                                 in
                              match uu____12064 with
                              | true  ->
                                  Some
                                    (let _0_1016 =
                                       FStar_Syntax_Print.bv_to_string x  in
                                     let _0_1015 =
                                       FStar_Syntax_Print.term_to_string
                                         x.FStar_Syntax_Syntax.sort
                                        in
                                     let _0_1014 =
                                       FStar_Syntax_Print.term_to_string t1
                                        in
                                     FStar_Util.format3 "%s : %s (%s)"
                                       _0_1016 _0_1015 _0_1014)
                              | uu____12066 -> None  in
                            let ax =
                              let a_name =
                                Some (Prims.strcat "binder_" xxsym)  in
                              FStar_SMTEncoding_Term.Assume
                                (t, a_name, a_name)
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____12078,t)) ->
                 let t_norm = whnf env t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____12087 = encode_free_var env fv t t_norm []  in
                 (match uu____12087 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____12106 = encode_sigelt env se  in
                 (match uu____12106 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____12116 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____12116 with | (uu____12128,decls,env) -> (decls, env)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15147  ->
            match uu____15147 with
            | (l,uu____15154,uu____15155) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15176  ->
            match uu____15176 with
            | (l,uu____15184,uu____15185) ->
                let uu____15190 =
                  FStar_All.pipe_left
                    (fun _0_1017  -> FStar_SMTEncoding_Term.Echo _0_1017)
                    (Prims.fst l)
                   in
                let _0_1019 =
                  let _0_1018 =
                    FStar_SMTEncoding_Term.Eval
                      (FStar_SMTEncoding_Util.mkFreeV l)
                     in
                  [_0_1018]  in
                _0_1020 :: _0_1019))
     in
  (prefix, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let _0_1023 =
      let _0_1022 =
        let _0_1021 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15208;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [_0_1022]  in
    FStar_ST.write last_env _0_1023
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____12237 = FStar_ST.read last_env  in
    match uu____12237 with
    | [] -> failwith "No env; call init first!"
    | e::uu____12243 ->
        let uu___157_12245 = e  in
        {
          bindings = (uu___157_12245.bindings);
          depth = (uu___157_12245.depth);
          tcenv;
          warn = (uu___157_12245.warn);
          cache = (uu___157_12245.cache);
          nolabels = (uu___157_12245.nolabels);
          use_zfuel_name = (uu___157_12245.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___157_12245.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____12249 = FStar_ST.read last_env  in
    match uu____12249 with
    | [] -> failwith "Empty env stack"
    | uu____12254::tl -> FStar_ST.write last_env (env :: tl)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____12262  ->
    let uu____12263 = FStar_ST.read last_env  in
    match uu____12263 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache  in
        let top =
          let uu___158_12284 = hd  in
          {
            bindings = (uu___162_15279.bindings);
            depth = (uu___162_15279.depth);
            tcenv = (uu___162_15279.tcenv);
            warn = (uu___162_15279.warn);
            cache = refs;
            nolabels = (uu___162_15279.nolabels);
            use_zfuel_name = (uu___162_15279.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_12284.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd :: tl)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____12290  ->
    let uu____12291 = FStar_ST.read last_env  in
    match uu____12291 with
    | [] -> failwith "Popping an empty stack"
    | uu____12296::tl -> FStar_ST.write last_env tl
  
let mark_env : Prims.unit -> Prims.unit = fun uu____12304  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____12307  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____12310  ->
    let uu____12311 = FStar_ST.read last_env  in
    match uu____12311 with
    | hd::uu____12317::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____12323 -> failwith "Impossible"
  
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
        let uu____12368 = FStar_Options.log_queries ()  in
        match uu____12368 with
        | true  ->
            let _0_1026 =
              FStar_SMTEncoding_Term.Caption
                (let _0_1025 =
                   let _0_1024 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Syntax_Print.lid_to_string)
                      in
                   FStar_All.pipe_right _0_1024 (FStar_String.concat ", ")
                    in
                 Prims.strcat "encoding sigelt " _0_1025)
               in
            _0_1026 :: decls
        | uu____12373 -> decls  in
      let env = get_env tcenv  in
      let uu____12375 = encode_sigelt env se  in
      match uu____12375 with
      | (decls,env) ->
          (set_env env; FStar_SMTEncoding_Z3.giveZ3 (caption decls))
  
let encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (match modul.FStar_Syntax_Syntax.is_interface with
           | true  -> "interface"
           | uu____12388 -> "module")
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____12390 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       match uu____12390 with
       | true  ->
           let _0_1027 =
             FStar_All.pipe_right
               (FStar_List.length modul.FStar_Syntax_Syntax.exports)
               FStar_Util.string_of_int
              in
           FStar_Util.print2
             "+++++++++++Encoding externals for %s ... %s exports\n" name
             _0_1027
       | uu____12393 -> ());
      (let env = get_env tcenv  in
       let uu____12395 =
         encode_signature
           (let uu___159_12399 = env  in
            {
              bindings = (uu___163_15403.bindings);
              depth = (uu___163_15403.depth);
              tcenv = (uu___163_15403.tcenv);
              warn = false;
              cache = (uu___163_15403.cache);
              nolabels = (uu___163_15403.nolabels);
              use_zfuel_name = (uu___163_15403.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___159_12399.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____12395 with
       | (decls,env) ->
           let caption decls =
             let uu____12411 = FStar_Options.log_queries ()  in
             match uu____12411 with
             | true  ->
                 let msg = Prims.strcat "Externals for " name  in
                 FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                   decls)
                   [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             | uu____12414 -> decls  in
           (set_env
              (let uu___160_12416 = env  in
               {
                 bindings = (uu___164_15420.bindings);
                 depth = (uu___164_15420.depth);
                 tcenv = (uu___164_15420.tcenv);
                 warn = true;
                 cache = (uu___164_15420.cache);
                 nolabels = (uu___164_15420.nolabels);
                 use_zfuel_name = (uu___164_15420.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___164_15420.encode_non_total_function_typ);
                 current_module_name = (uu___164_15420.current_module_name)
               });
            (let uu____12418 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             match uu____12418 with
             | true  ->
                 FStar_Util.print1 "Done encoding externals for %s\n" name
             | uu____12419 -> ());
            (let decls = caption decls  in FStar_SMTEncoding_Z3.giveZ3 decls)))
  
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
        FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
          (FStar_TypeChecker_Env.current_module tcenv).FStar_Ident.str;
        (let env = get_env tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____12460 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____12481 = aux rest  in
                 (match uu____12481 with
                  | (out,rest) ->
                      let t =
                        let uu____15506 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15506 with
                        | Some uu____15510 ->
                            let uu____15511 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15511
                              x.FStar_Syntax_Syntax.sort
                        | uu____15512 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort
                         in
                      let _0_1029 =
                        let _0_1028 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___161_12499 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___165_15518.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___161_12499.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             })
                           in
                        _0_1028 :: out  in
                      (_0_1029, rest))
             | uu____12500 -> ([], bindings)  in
           let uu____12504 = aux bindings  in
           match uu____12504 with
           | (closing,bindings) ->
               let _0_1030 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q
                  in
               (_0_1030, bindings)
            in
         match uu____12460 with
         | (q,bindings) ->
             let uu____12530 =
               let _0_1031 =
                 FStar_List.filter
                   (fun uu___134_15557  ->
                      match uu___134_15557 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15558 ->
                          false
                      | uu____12538 -> true) bindings
                  in
               encode_env_bindings env _0_1031  in
             (match uu____12530 with
              | (env_decls,env) ->
                  ((let uu____12549 =
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
                    match uu____12549 with
                    | true  ->
                        let _0_1032 = FStar_Syntax_Print.term_to_string q  in
                        FStar_Util.print1 "Encoding query formula: %s\n"
                          _0_1032
                    | uu____12550 -> ());
                   (let uu____12551 = encode_formula q env  in
                    match uu____12551 with
                    | (phi,qdecls) ->
                        let uu____12563 =
                          let _0_1033 = FStar_TypeChecker_Env.get_range tcenv
                             in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg _0_1033 phi
                           in
                        (match uu____12563 with
                         | (labels,phi) ->
                             let uu____12575 = encode_labels labels  in
                             (match uu____12575 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_1035 =
                                         FStar_SMTEncoding_Util.mkNot phi  in
                                       let _0_1034 =
                                         Some (varops.mk_unique "@query")  in
                                       (_0_1035, (Some "query"), _0_1034))
                                     in
                                  let suffix =
                                    let uu____15631 =
                                      let uu____15633 =
                                        let uu____15635 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        match uu____12600 with
                                        | true  ->
                                            [FStar_SMTEncoding_Term.PrintStats]
                                        | uu____12602 -> []  in
                                      FStar_List.append _0_1036
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix _0_1037
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____12613 = encode_formula q env  in
       match uu____12613 with
       | (f,uu____12617) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____12619) -> true
             | uu____12622 -> false)))
  