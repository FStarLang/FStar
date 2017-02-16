open Prims
let add_fuel x tl =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
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
          FStar_Syntax_Syntax.ppname = _0_267;
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
              fun value  -> fun v  -> FStar_Util.smap_add next1 key value) ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next2 key value) ();
         FStar_ST.write scopes ((next1, next2) :: tl))
    | uu____664 -> failwith "Impossible"  in
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
let unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___135_673 = x  in
    let _0_293 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = _0_293;
      FStar_Syntax_Syntax.index = (uu___135_673.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___135_673.FStar_Syntax_Syntax.sort)
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
    let _0_294 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___110_840  ->
              match uu___110_840 with
              | Binding_var (x,uu____842) ->
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
           tcenv = (uu___136_901.tcenv);
           warn = (uu___136_901.warn);
           cache = (uu___136_901.cache);
           nolabels = (uu___136_901.nolabels);
           use_zfuel_name = (uu___136_901.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___136_901.encode_non_total_function_typ)
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
           depth = (uu___137_914.depth);
           tcenv = (uu___137_914.tcenv);
           warn = (uu___137_914.warn);
           cache = (uu___137_914.cache);
           nolabels = (uu___137_914.nolabels);
           use_zfuel_name = (uu___137_914.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_914.encode_non_total_function_typ)
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
             depth = (uu___138_930.depth);
             tcenv = (uu___138_930.tcenv);
             warn = (uu___138_930.warn);
             cache = (uu___138_930.cache);
             nolabels = (uu___138_930.nolabels);
             use_zfuel_name = (uu___138_930.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___138_930.encode_non_total_function_typ)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___139_940 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___139_940.depth);
          tcenv = (uu___139_940.tcenv);
          warn = (uu___139_940.warn);
          cache = (uu___139_940.cache);
          nolabels = (uu___139_940.nolabels);
          use_zfuel_name = (uu___139_940.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___139_940.encode_non_total_function_typ)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___111_956  ->
             match uu___111_956 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____964 -> None)
         in
      let uu____967 = aux a  in
      match uu____967 with
      | None  ->
          let a2 = unmangle a  in
          let uu____974 = aux a2  in
          (match uu____974 with
           | None  ->
               failwith
                 (let _0_298 = FStar_Syntax_Print.bv_to_string a2  in
                  let _0_297 = print_env env  in
                  FStar_Util.format2
                    "Bound term variable not found (after unmangling): %s in environment: %s"
                    _0_298 _0_297)
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let _0_304 =
        let uu___140_999 = env  in
        let _0_303 =
          let _0_302 =
            Binding_fvar
              (let _0_301 =
                 let _0_300 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                 FStar_All.pipe_left (fun _0_299  -> Some _0_299) _0_300  in
               (x, fname, _0_301, None))
             in
          _0_302 :: (env.bindings)  in
        {
          bindings = _0_303;
          depth = (uu___140_999.depth);
          tcenv = (uu___140_999.tcenv);
          warn = (uu___140_999.warn);
          cache = (uu___140_999.cache);
          nolabels = (uu___140_999.nolabels);
          use_zfuel_name = (uu___140_999.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_999.encode_non_total_function_typ)
        }  in
      (fname, ftok, _0_304)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___112_1021  ->
           match uu___112_1021 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1043 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let _0_305 =
        lookup_binding env
          (fun uu___113_1056  ->
             match uu___113_1056 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1066 -> None)
         in
      FStar_All.pipe_right _0_305 FStar_Option.isSome
  
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
            (let _0_306 = FStar_Syntax_Print.lid_to_string a  in
             FStar_Util.format1 "Name not found: %s" _0_306)
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
            depth = (uu___141_1125.depth);
            tcenv = (uu___141_1125.tcenv);
            warn = (uu___141_1125.warn);
            cache = (uu___141_1125.cache);
            nolabels = (uu___141_1125.nolabels);
            use_zfuel_name = (uu___141_1125.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___141_1125.encode_non_total_function_typ)
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
                (let _0_308 =
                   let _0_307 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                      in
                   [_0_307]  in
                 (f, _0_308))
               in
            let uu___142_1153 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___142_1153.depth);
              tcenv = (uu___142_1153.tcenv);
              warn = (uu___142_1153.warn);
              cache = (uu___142_1153.cache);
              nolabels = (uu___142_1153.nolabels);
              use_zfuel_name = (uu___142_1153.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___142_1153.encode_non_total_function_typ)
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
           | uu____1190 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1195,fuel::[]) ->
                         let uu____1198 =
                           let _0_310 =
                             let _0_309 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right _0_309 Prims.fst  in
                           FStar_Util.starts_with _0_310 "fuel"  in
                         (match uu____1198 with
                          | true  ->
                              let _0_313 =
                                let _0_312 =
                                  FStar_SMTEncoding_Util.mkFreeV
                                    (name, FStar_SMTEncoding_Term.Term_sort)
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF _0_312 fuel
                                 in
                              FStar_All.pipe_left
                                (fun _0_311  -> Some _0_311) _0_313
                          | uu____1201 -> Some t)
                     | uu____1202 -> Some t)
                | uu____1203 -> None))
  
let lookup_free_var env a =
  let uu____1221 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1221 with
  | Some t -> t
  | None  ->
      failwith
        (let _0_314 =
           FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
         FStar_Util.format1 "Name not found: %s" _0_314)
  
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
             FStar_SMTEncoding_Term.freevars = uu____1293;
             FStar_SMTEncoding_Term.rng = uu____1294;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1302 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym ->
                (match sym.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1316 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_1325  ->
           match uu___114_1325 with
           | Binding_fvar (uu____1327,nm',tok,uu____1330) when nm = nm' ->
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
                            let _0_315 = add_fuel [guard]  in
                            FStar_All.pipe_right _0_315 FStar_List.hd
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
          let _0_316 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_316 FStar_Option.isNone
      | uu____1461 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1468 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____1468 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1469,uu____1470,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_1499  ->
                  match uu___115_1499 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1500 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1501,uu____1502,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let _0_317 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_317 FStar_Option.isSome
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
    let _0_320 = let _0_318 = FStar_Syntax_Syntax.null_binder t  in [_0_318]
       in
    let _0_319 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs _0_320 _0_319 None
  
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
                    let _0_321 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out _0_321
                | s ->
                    let _0_322 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out _0_322) e)
  
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
        let rec aux t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1624;
                       FStar_SMTEncoding_Term.rng = uu____1625;_}::[]),x::xs)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1639) ->
              let uu____1644 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v  ->
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
          (let _0_324 =
             let _0_323 =
               FStar_SMTEncoding_Term.boxInt
                 (FStar_SMTEncoding_Util.mkInteger'
                    (FStar_Util.int_of_char c))
                in
             [_0_323]  in
           ("FStar.Char.Char", _0_324))
    | FStar_Const.Const_int (i,None ) ->
        FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger i)
    | FStar_Const.Const_int (i,Some uu____1761) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1770) ->
        varops.string_const
          (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        failwith
          (let _0_325 = FStar_Syntax_Print.const_to_string c  in
           FStar_Util.format1 "Unhandled constant: %s" _0_325)
  
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
            let _0_326 = FStar_Syntax_Util.unrefine t  in aux true _0_326
        | uu____1807 ->
            (match norm with
             | true  -> let _0_327 = whnf env t  in aux false _0_327
             | uu____1808 ->
                 failwith
                   (let _0_329 =
                      FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos
                       in
                    let _0_328 = FStar_Syntax_Print.term_to_string t0  in
                    FStar_Util.format2 "(%s) Expected a function typ; got %s"
                      _0_329 _0_328))
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
        let _0_330 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_330)
  
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
             let _0_331 = FStar_Syntax_Print.binders_to_string ", " bs  in
             FStar_Util.print1 "Encoding binders %s\n" _0_331
         | uu____1973 -> ());
        (let uu____1974 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2010  ->
                   fun b  ->
                     match uu____2010 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2053 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2062 = gen_term_var env x  in
                           match uu____2062 with
                           | (xxsym,xx,env') ->
                               let uu____2076 =
                                 let _0_332 =
                                   norm env x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt _0_332 env xx  in
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
              let _0_333 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t  in
              (_0_333, decls)

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
                   let _0_334 = FStar_SMTEncoding_Term.mk_HasTypeZ e t  in
                   (_0_334, decls)
               | Some f ->
                   let _0_335 = FStar_SMTEncoding_Term.mk_HasTypeFuel f e t
                      in
                   (_0_335, decls))

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
           let _0_338 = FStar_Syntax_Print.tag_of_term t  in
           let _0_337 = FStar_Syntax_Print.tag_of_term t0  in
           let _0_336 = FStar_Syntax_Print.term_to_string t0  in
           FStar_Util.print3 "(%s) (%s)   %s\n" _0_338 _0_337 _0_336
       | uu____2197 -> ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           failwith
             (let _0_342 =
                FStar_All.pipe_left FStar_Range.string_of_range
                  t.FStar_Syntax_Syntax.pos
                 in
              let _0_341 = FStar_Syntax_Print.tag_of_term t0  in
              let _0_340 = FStar_Syntax_Print.term_to_string t0  in
              let _0_339 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_342
                _0_341 _0_340 _0_339)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           failwith
             (let _0_343 = FStar_Syntax_Print.bv_to_string x  in
              FStar_Util.format1 "Impossible: locally nameless; got %s"
                _0_343)
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2208) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2228) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x  in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let _0_344 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name  in
           (_0_344, [])
       | FStar_Syntax_Syntax.Tm_type uu____2242 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t,uu____2245) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let _0_345 = encode_const c  in (_0_345, [])
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
                            let _0_346 = varops.fresh "f"  in
                            (_0_346, FStar_SMTEncoding_Term.Term_sort)  in
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
                                          let _0_347 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards
                                             in
                                          (_0_347, [])
                                      | Some pre ->
                                          let uu____2328 =
                                            encode_formula pre env'  in
                                          (match uu____2328 with
                                           | (guard,decls0) ->
                                               let _0_348 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (guard :: guards)
                                                  in
                                               (_0_348, decls0))
                                       in
                                    (match uu____2319 with
                                     | (guards,guard_decls) ->
                                         let t_interp =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_349 =
                                                FStar_SMTEncoding_Util.mkImp
                                                  (guards, res_pred)
                                                 in
                                              ([[app]], vars, _0_349))
                                            in
                                         let cvars =
                                           let _0_350 =
                                             FStar_SMTEncoding_Term.free_variables
                                               t_interp
                                              in
                                           FStar_All.pipe_right _0_350
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
                                              let _0_352 =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (let _0_351 =
                                                     FStar_All.pipe_right
                                                       cvars
                                                       (FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV)
                                                      in
                                                   (t', _0_351))
                                                 in
                                              (_0_352, [])
                                          | None  ->
                                              let tsym =
                                                varops.mk_unique
                                                  (let _0_353 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.strcat "Tm_arrow_"
                                                     _0_353)
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
                                                  (let _0_354 =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       cvars
                                                      in
                                                   (tsym, _0_354))
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
                                                  (let _0_355 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[t_has_kind]],
                                                         cvars, t_has_kind)
                                                      in
                                                   (_0_355, a_name, a_name))
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
                                                  (let _0_359 =
                                                     mkForall_fuel
                                                       (let _0_358 =
                                                          FStar_SMTEncoding_Util.mkImp
                                                            (let _0_357 =
                                                               let _0_356 =
                                                                 FStar_SMTEncoding_Term.mk_PreType
                                                                   f
                                                                  in
                                                               FStar_SMTEncoding_Term.mk_tester
                                                                 "Tm_arrow"
                                                                 _0_356
                                                                in
                                                             (f_has_t,
                                                               _0_357))
                                                           in
                                                        ([[f_has_t]], (fsym
                                                          :: cvars), _0_358))
                                                      in
                                                   (_0_359,
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
                                                  (let _0_361 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_360 =
                                                          FStar_SMTEncoding_Util.mkIff
                                                            (f_has_t_z,
                                                              t_interp)
                                                           in
                                                        ([[f_has_t_z]], (fsym
                                                          :: cvars), _0_360))
                                                      in
                                                   (_0_361, a_name, a_name))
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
                         (let _0_362 =
                            FStar_SMTEncoding_Term.mk_HasType t
                              FStar_SMTEncoding_Term.mk_Term_type
                             in
                          (_0_362, (Some "Typing for non-total arrows"),
                            a_name))
                        in
                     let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                     let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                     let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t  in
                     let t_interp =
                       let a_name = Some (Prims.strcat "pre_typing_" tsym)
                          in
                       FStar_SMTEncoding_Term.Assume
                         (let _0_366 =
                            mkForall_fuel
                              (let _0_365 =
                                 FStar_SMTEncoding_Util.mkImp
                                   (let _0_364 =
                                      let _0_363 =
                                        FStar_SMTEncoding_Term.mk_PreType f
                                         in
                                      FStar_SMTEncoding_Term.mk_tester
                                        "Tm_arrow" _0_363
                                       in
                                    (f_has_t, _0_364))
                                  in
                               ([[f_has_t]], [fsym], _0_365))
                             in
                          (_0_366, a_name, a_name))
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
                      let _0_367 = Prims.fst (FStar_List.hd b)  in
                      (_0_367, f))
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
                               let uu____2584 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2584 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (let _0_368 =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm base_t
                                            in
                                         (_0_368, refinement))
                                       in
                                    let cvars =
                                      let _0_369 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right _0_369
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
                                         let _0_371 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_370 =
                                                FStar_All.pipe_right cvars
                                                  (FStar_List.map
                                                     FStar_SMTEncoding_Util.mkFreeV)
                                                 in
                                              (t, _0_370))
                                            in
                                         (_0_371, [])
                                     | None  ->
                                         let tsym =
                                           varops.mk_unique
                                             (let _0_372 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "Tm_refine_"
                                                _0_372)
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
                                             (let _0_373 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (tsym, _0_373))
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
                                             (let _0_375 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_374 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (t_haseq_ref,
                                                         t_haseq_base)
                                                      in
                                                   ([[t_haseq_ref]], cvars,
                                                     _0_374))
                                                 in
                                              (_0_375,
                                                (Some
                                                   (Prims.strcat "haseq for "
                                                      tsym)),
                                                (Some
                                                   (Prims.strcat "haseq" tsym))))
                                            in
                                         let t_kinding =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_376 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  ([[t_has_kind]], cvars,
                                                    t_has_kind)
                                                 in
                                              (_0_376,
                                                (Some "refinement kinding"),
                                                (Some
                                                   (Prims.strcat
                                                      "refinement_kinding_"
                                                      tsym))))
                                            in
                                         let t_interp =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_379 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_377 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (x_has_t, encoding)
                                                      in
                                                   ([[x_has_t]], (ffv :: xfv
                                                     :: cvars), _0_377))
                                                 in
                                              let _0_378 =
                                                Some
                                                  (FStar_Syntax_Print.term_to_string
                                                     t0)
                                                 in
                                              (_0_379, _0_378,
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
                                          (t, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             FStar_SMTEncoding_Util.mk_Term_uvar (FStar_Unionfind.uvar_id uv)
              in
           let uu____2742 = encode_term_pred None k env ttm  in
           (match uu____2742 with
            | (t_has_k,decls) ->
                let d =
                  FStar_SMTEncoding_Term.Assume
                    (let _0_382 =
                       Some
                         (varops.mk_unique
                            (let _0_381 =
                               let _0_380 = FStar_Unionfind.uvar_id uv  in
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 _0_380
                                in
                             FStar_Util.format1 "uvar_typing_%s" _0_381))
                        in
                     (t_has_k, (Some "Uvar typing"), _0_382))
                   in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____2756 ->
           let uu____2766 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____2766 with
            | (head,args_e) ->
                let uu____2794 =
                  let _0_383 =
                    (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                     in
                  (_0_383, args_e)  in
                (match uu____2794 with
                 | (uu____2809,uu____2810) when head_redex env head ->
                     let _0_384 = whnf env t  in encode_term _0_384 env
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
                               let _0_385 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2  in
                               (_0_385, (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____2909) ->
                     let e0 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_387 =
                                let _0_386 = FStar_List.hd args_e  in
                                [_0_386]  in
                              (head, _0_387)))) None
                         head.FStar_Syntax_Syntax.pos
                        in
                     ((let uu____2951 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       match uu____2951 with
                       | true  ->
                           let _0_388 = FStar_Syntax_Print.term_to_string e0
                              in
                           FStar_Util.print1 "Trying to normalize %s\n"
                             _0_388
                       | uu____2952 -> ());
                      (let e0 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0
                          in
                       (let uu____2955 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        match uu____2955 with
                        | true  ->
                            let _0_389 = FStar_Syntax_Print.term_to_string e0
                               in
                            FStar_Util.print1 "Result of normalization %s\n"
                              _0_389
                        | uu____2956 -> ());
                       (let e0 =
                          let uu____2958 =
                            let uu____2959 =
                              (FStar_Syntax_Subst.compress e0).FStar_Syntax_Syntax.n
                               in
                            match uu____2959 with
                            | FStar_Syntax_Syntax.Tm_app uu____2960 -> false
                            | uu____2970 -> true  in
                          match uu____2958 with
                          | true  -> e0
                          | uu____2971 ->
                              let uu____2972 =
                                FStar_Syntax_Util.head_and_args e0  in
                              (match uu____2972 with
                               | (head,args) ->
                                   let uu____2998 =
                                     let uu____2999 =
                                       (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                                        in
                                     match uu____2999 with
                                     | FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_reify ) -> true
                                     | uu____3000 -> false  in
                                   (match uu____2998 with
                                    | true  ->
                                        (match args with
                                         | x::[] -> Prims.fst x
                                         | uu____3016 ->
                                             failwith
                                               "Impossible : Reify applied to multiple arguments after normalization.")
                                    | uu____3022 -> e0))
                           in
                        let e =
                          match args_e with
                          | uu____3024::[] -> e0
                          | uu____3037 ->
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (let _0_390 = FStar_List.tl args_e  in
                                     (e0, _0_390)))) None
                                t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3060),(arg,uu____3062)::[]) -> encode_term arg env
                 | uu____3080 ->
                     let uu____3088 = encode_args args_e env  in
                     (match uu____3088 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3121 = encode_term head env  in
                            match uu____3121 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3160 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3160 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3202  ->
                                                 fun uu____3203  ->
                                                   match (uu____3202,
                                                           uu____3203)
                                                   with
                                                   | ((bv,uu____3217),
                                                      (a,uu____3219)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e
                                             in
                                          let ty =
                                            let _0_391 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right _0_391
                                              (FStar_Syntax_Subst.subst subst)
                                             in
                                          let uu____3235 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3235 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_394 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        ([[has_type]], cvars,
                                                          has_type)
                                                       in
                                                    let _0_393 =
                                                      Some
                                                        (varops.mk_unique
                                                           (let _0_392 =
                                                              FStar_Util.digest_of_string
                                                                (FStar_SMTEncoding_Term.hash_of_term
                                                                   app_tm)
                                                               in
                                                            Prims.strcat
                                                              "partial_app_typing_"
                                                              _0_392))
                                                       in
                                                    (_0_394,
                                                      (Some
                                                         "Partial app typing"),
                                                      _0_393))
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3266 = lookup_free_var_sym env fv  in
                            match uu____3266 with
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
                                Some
                                  (let _0_395 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right _0_395 Prims.snd)
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3310,FStar_Util.Inl t,uu____3312) ->
                                Some t
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3333,FStar_Util.Inr c,uu____3335) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3356 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type ->
                               let head_type =
                                 let _0_396 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine _0_396
                                  in
                               let uu____3376 =
                                 curried_arrow_formals_comp head_type  in
                               (match uu____3376 with
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
                                     | uu____3401 ->
                                         (match (FStar_List.length formals) >
                                                  (FStar_List.length args)
                                          with
                                          | true  ->
                                              encode_partial_app
                                                (Some (formals, c))
                                          | uu____3413 ->
                                              encode_partial_app None)))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3446 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3446 with
            | (bs,body,opening) ->
                let fallback uu____3461 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let _0_397 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (_0_397, [decl])  in
                let is_impure uu___118_3475 =
                  match uu___118_3475 with
                  | FStar_Util.Inl lc ->
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
                  | FStar_Util.Inr (eff,uu____3486) ->
                      let _0_398 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right _0_398 Prims.op_Negation
                   in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let _0_401 =
                        let _0_399 = lc.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening _0_399  in
                      FStar_All.pipe_right _0_401
                        (fun _0_400  -> Some _0_400)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar uu____3523 =
                        let _0_402 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right _0_402 Prims.fst  in
                      (match FStar_Ident.lid_equals eff
                               FStar_Syntax_Const.effect_Tot_lid
                       with
                       | true  ->
                           let _0_404 =
                             FStar_Syntax_Syntax.mk_Total (new_uvar ())  in
                           FStar_All.pipe_right _0_404
                             (fun _0_403  -> Some _0_403)
                       | uu____3530 ->
                           (match FStar_Ident.lid_equals eff
                                    FStar_Syntax_Const.effect_GTot_lid
                            with
                            | true  ->
                                let _0_406 =
                                  FStar_Syntax_Syntax.mk_GTotal (new_uvar ())
                                   in
                                FStar_All.pipe_right _0_406
                                  (fun _0_405  -> Some _0_405)
                            | uu____3533 -> None))
                   in
                (match lopt with
                 | None  ->
                     ((let _0_408 =
                         let _0_407 = FStar_Syntax_Print.term_to_string t0
                            in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           _0_407
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_408);
                      fallback ())
                 | Some lc ->
                     let uu____3553 = is_impure lc  in
                     (match uu____3553 with
                      | true  -> fallback ()
                      | uu____3556 ->
                          let uu____3557 = encode_binders None bs env  in
                          (match uu____3557 with
                           | (vars,guards,envbody,decls,uu____3572) ->
                               let uu____3579 = encode_term body envbody  in
                               (match uu____3579 with
                                | (body,decls') ->
                                    let key_body =
                                      FStar_SMTEncoding_Util.mkForall
                                        (let _0_410 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (let _0_409 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (_0_409, body))
                                            in
                                         ([], vars, _0_410))
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
                                    let uu____3597 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____3597 with
                                     | Some (t,uu____3612,uu____3613) ->
                                         let _0_412 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_411 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (t, _0_411))
                                            in
                                         (_0_412, [])
                                     | None  ->
                                         let uu____3632 =
                                           is_eta env vars body  in
                                         (match uu____3632 with
                                          | Some t -> (t, [])
                                          | None  ->
                                              let cvar_sorts =
                                                FStar_List.map Prims.snd
                                                  cvars
                                                 in
                                              let fsym =
                                                varops.mk_unique
                                                  (let _0_413 =
                                                     FStar_Util.digest_of_string
                                                       tkey_hash
                                                      in
                                                   Prims.strcat "Tm_abs_"
                                                     _0_413)
                                                 in
                                              let fdecl =
                                                FStar_SMTEncoding_Term.DeclFun
                                                  (fsym, cvar_sorts,
                                                    FStar_SMTEncoding_Term.Term_sort,
                                                    None)
                                                 in
                                              let f =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (let _0_414 =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       cvars
                                                      in
                                                   (fsym, _0_414))
                                                 in
                                              let app = mk_Apply f vars  in
                                              let typing_f =
                                                let uu____3653 =
                                                  codomain_eff lc  in
                                                match uu____3653 with
                                                | None  -> []
                                                | Some c ->
                                                    let tfun =
                                                      FStar_Syntax_Util.arrow
                                                        bs c
                                                       in
                                                    let uu____3660 =
                                                      encode_term_pred None
                                                        tfun env f
                                                       in
                                                    (match uu____3660 with
                                                     | (f_has_t,decls'') ->
                                                         let a_name =
                                                           Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                fsym)
                                                            in
                                                         let _0_417 =
                                                           let _0_416 =
                                                             FStar_SMTEncoding_Term.Assume
                                                               (let _0_415 =
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                   in
                                                                (_0_415,
                                                                  a_name,
                                                                  a_name))
                                                              in
                                                           [_0_416]  in
                                                         FStar_List.append
                                                           decls'' _0_417)
                                                 in
                                              let interp_f =
                                                let a_name =
                                                  Some
                                                    (Prims.strcat
                                                       "interpretation_" fsym)
                                                   in
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_419 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_418 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars),
                                                          _0_418))
                                                      in
                                                   (_0_419, a_name, a_name))
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
           ((uu____3695,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____3696;
                          FStar_Syntax_Syntax.lbunivs = uu____3697;
                          FStar_Syntax_Syntax.lbtyp = uu____3698;
                          FStar_Syntax_Syntax.lbeff = uu____3699;
                          FStar_Syntax_Syntax.lbdef = uu____3700;_}::uu____3701),uu____3702)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____3720;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____3722;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____3738 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let _0_420 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (_0_420, [decl_e])))
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
              let uu____3792 = encode_term e1 env  in
              match uu____3792 with
              | (ee1,decls1) ->
                  let uu____3799 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____3799 with
                   | (xs,e2) ->
                       let uu____3813 = FStar_List.hd xs  in
                       (match uu____3813 with
                        | (x,uu____3821) ->
                            let env' = push_term_var env x ee1  in
                            let uu____3823 = encode_body e2 env'  in
                            (match uu____3823 with
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
            let uu____3845 =
              let _0_421 =
                FStar_Syntax_Syntax.null_bv
                  ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                     None FStar_Range.dummyRange)
                 in
              gen_term_var env _0_421  in
            match uu____3845 with
            | (scrsym,scr',env) ->
                let uu____3870 = encode_term e env  in
                (match uu____3870 with
                 | (scr,decls) ->
                     let uu____3877 =
                       let encode_branch b uu____3893 =
                         match uu____3893 with
                         | (else_case,decls) ->
                             let uu____3904 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____3904 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p  in
                                  FStar_List.fold_right
                                    (fun uu____3934  ->
                                       fun uu____3935  ->
                                         match (uu____3934, uu____3935) with
                                         | ((env0,pattern),(else_case,decls))
                                             ->
                                             let guard = pattern.guard scr'
                                                in
                                             let projections =
                                               pattern.projections scr'  in
                                             let env =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____3972  ->
                                                         match uu____3972
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env)
                                                in
                                             let uu____3977 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____3992 =
                                                     encode_term w env  in
                                                   (match uu____3992 with
                                                    | (w,decls2) ->
                                                        let _0_424 =
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            (let _0_423 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_422
                                                                    =
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                     in
                                                                  (w, _0_422))
                                                                in
                                                             (guard, _0_423))
                                                           in
                                                        (_0_424, decls2))
                                                in
                                             (match uu____3977 with
                                              | (guard,decls2) ->
                                                  let uu____4007 =
                                                    encode_br br env  in
                                                  (match uu____4007 with
                                                   | (br,decls3) ->
                                                       let _0_425 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case)
                                                          in
                                                       (_0_425,
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____3877 with
                      | (match_tm,decls) ->
                          let _0_426 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (_0_426, decls)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4056 -> let _0_427 = encode_one_pat env pat  in [_0_427]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4066 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       match uu____4066 with
       | true  ->
           let _0_428 = FStar_Syntax_Print.pat_to_string pat  in
           FStar_Util.print1 "Encoding pattern %s\n" _0_428
       | uu____4067 -> ());
      (let uu____4068 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4068 with
       | (vars,pat_term) ->
           let uu____4078 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4101  ->
                     fun v  ->
                       match uu____4101 with
                       | (env,vars) ->
                           let uu____4129 = gen_term_var env v  in
                           (match uu____4129 with
                            | (xx,uu____4141,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, []))
              in
           (match uu____4078 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4188 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_429 = encode_const c  in (scrutinee, _0_429))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4214 =
                          FStar_TypeChecker_Env.datacons_of_typ env.tcenv
                            tc_name
                           in
                        match uu____4214 with
                        | (uu____4218,uu____4219::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4221 ->
                            mk_data_tester env
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4242  ->
                                  match uu____4242 with
                                  | (arg,uu____4248) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_430 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg _0_430))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4276 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4291 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let _0_432 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4330  ->
                                  match uu____4330 with
                                  | (arg,uu____4339) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_431 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg _0_431))
                         in
                      FStar_All.pipe_right _0_432 FStar_List.flatten
                   in
                let pat_term uu____4357 = encode_term pat_term env  in
                let pattern =
                  {
                    pat_vars = vars;
                    pat_term;
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
      let uu____4364 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4379  ->
                fun uu____4380  ->
                  match (uu____4379, uu____4380) with
                  | ((tms,decls),(t,uu____4400)) ->
                      let uu____4411 = encode_term t env  in
                      (match uu____4411 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____4364 with | (l,decls) -> ((FStar_List.rev l), decls)

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
            let uu____4449 = FStar_Syntax_Util.list_elements e  in
            match uu____4449 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____4467 =
              let _0_433 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right _0_433 FStar_Syntax_Util.head_and_args  in
            match uu____4467 with
            | (head,args) ->
                let uu____4507 =
                  let _0_434 =
                    (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                     in
                  (_0_434, args)  in
                (match uu____4507 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____4526,uu____4527)::(e,uu____4529)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4560)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____4581 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements p  in
            let smt_pat_or t =
              let uu____4614 =
                let _0_435 = FStar_Syntax_Util.unmeta t  in
                FStar_All.pipe_right _0_435 FStar_Syntax_Util.head_and_args
                 in
              match uu____4614 with
              | (head,args) ->
                  let uu____4652 =
                    let _0_436 =
                      (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                       in
                    (_0_436, args)  in
                  (match uu____4652 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4670)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____4690 -> None)
               in
            match elts with
            | t::[] ->
                let uu____4708 = smt_pat_or t  in
                (match uu____4708 with
                 | Some e ->
                     let _0_438 = list_elements e  in
                     FStar_All.pipe_right _0_438
                       (FStar_List.map
                          (fun branch  ->
                             let _0_437 = list_elements branch  in
                             FStar_All.pipe_right _0_437
                               (FStar_List.map one_pat)))
                 | uu____4751 ->
                     let _0_439 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [_0_439])
            | uu____4779 ->
                let _0_440 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [_0_440]
             in
          let uu____4805 =
            let uu____4821 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____4821 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4849 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____4849 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____4884;
                            FStar_Syntax_Syntax.effect_name = uu____4885;
                            FStar_Syntax_Syntax.result_typ = uu____4886;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____4888)::(post,uu____4890)::(pats,uu____4892)::[];
                            FStar_Syntax_Syntax.flags = uu____4893;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let _0_441 = lemma_pats pats'  in
                          (binders, pre, post, _0_441)
                      | uu____4938 -> failwith "impos"))
            | uu____4954 -> failwith "Impos"  in
          match uu____4805 with
          | (binders,pre,post,patterns) ->
              let uu____4998 = encode_binders None binders env  in
              (match uu____4998 with
               | (vars,guards,env,decls,uu____5013) ->
                   let uu____5020 =
                     let _0_443 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch  ->
                               let uu____5063 =
                                 let _0_442 =
                                   FStar_All.pipe_right branch
                                     (FStar_List.map
                                        (fun uu____5087  ->
                                           match uu____5087 with
                                           | (t,uu____5094) ->
                                               encode_term t
                                                 (let uu___144_5097 = env  in
                                                  {
                                                    bindings =
                                                      (uu___144_5097.bindings);
                                                    depth =
                                                      (uu___144_5097.depth);
                                                    tcenv =
                                                      (uu___144_5097.tcenv);
                                                    warn =
                                                      (uu___144_5097.warn);
                                                    cache =
                                                      (uu___144_5097.cache);
                                                    nolabels =
                                                      (uu___144_5097.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___144_5097.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right _0_442 FStar_List.unzip
                                  in
                               match uu____5063 with
                               | (pats,decls) -> (pats, decls)))
                        in
                     FStar_All.pipe_right _0_443 FStar_List.unzip  in
                   (match uu____5020 with
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
                                           let _0_445 =
                                             let _0_444 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               _0_444 e
                                              in
                                           _0_445 :: p))
                               | uu____5143 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let _0_446 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e
                                                    in
                                                 _0_446 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let _0_448 =
                                           let _0_447 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             _0_447 tl
                                            in
                                         aux _0_448 vars
                                     | uu____5179 -> pats  in
                                   let _0_449 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux _0_449 vars)
                           in
                        let env =
                          let uu___145_5184 = env  in
                          {
                            bindings = (uu___145_5184.bindings);
                            depth = (uu___145_5184.depth);
                            tcenv = (uu___145_5184.tcenv);
                            warn = (uu___145_5184.warn);
                            cache = (uu___145_5184.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___145_5184.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___145_5184.encode_non_total_function_typ)
                          }  in
                        let uu____5185 =
                          let _0_450 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula _0_450 env  in
                        (match uu____5185 with
                         | (pre,decls'') ->
                             let uu____5192 =
                               let _0_451 = FStar_Syntax_Util.unmeta post  in
                               encode_formula _0_451 env  in
                             (match uu____5192 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let _0_454 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_453 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (let _0_452 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (pre :: guards)
                                               in
                                            (_0_452, post))
                                          in
                                       (pats, vars, _0_453))
                                     in
                                  (_0_454, decls)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug phi =
        let uu____5213 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        match uu____5213 with
        | true  ->
            let _0_456 = FStar_Syntax_Print.tag_of_term phi  in
            let _0_455 = FStar_Syntax_Print.term_to_string phi  in
            FStar_Util.print2 "Formula (%s)  %s\n" _0_456 _0_455
        | uu____5214 -> ()  in
      let enc f r l =
        let uu____5240 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5253 = encode_term (Prims.fst x) env  in
                 match uu____5253 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5240 with
        | (decls,args) ->
            let _0_457 =
              let uu___146_5271 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___146_5271.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___146_5271.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_457, decls)
         in
      let const_op f r uu____5289 = let _0_458 = f r  in (_0_458, [])  in
      let un_op f l =
        let _0_459 = FStar_List.hd l  in FStar_All.pipe_left f _0_459  in
      let bin_op f uu___119_5319 =
        match uu___119_5319 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5327 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____5354 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5363  ->
                 match uu____5363 with
                 | (t,uu____5371) ->
                     let uu____5372 = encode_formula t env  in
                     (match uu____5372 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l
           in
        match uu____5354 with
        | (decls,phis) ->
            let _0_460 =
              let uu___147_5390 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___147_5390.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___147_5390.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_460, decls)
         in
      let eq_op r uu___120_5405 =
        match uu___120_5405 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r [e1; e2]
        | l -> (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l  in
      let mk_imp r uu___121_5490 =
        match uu___121_5490 with
        | (lhs,uu____5494)::(rhs,uu____5496)::[] ->
            let uu____5517 = encode_formula rhs env  in
            (match uu____5517 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____5526) ->
                      (l1, decls1)
                  | uu____5529 ->
                      let uu____5530 = encode_formula lhs env  in
                      (match uu____5530 with
                       | (l2,decls2) ->
                           let _0_461 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (_0_461, (FStar_List.append decls1 decls2)))))
        | uu____5538 -> failwith "impossible"  in
      let mk_ite r uu___122_5553 =
        match uu___122_5553 with
        | (guard,uu____5557)::(_then,uu____5559)::(_else,uu____5561)::[] ->
            let uu____5590 = encode_formula guard env  in
            (match uu____5590 with
             | (g,decls1) ->
                 let uu____5597 = encode_formula _then env  in
                 (match uu____5597 with
                  | (t,decls2) ->
                      let uu____5604 = encode_formula _else env  in
                      (match uu____5604 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____5613 -> failwith "impossible"  in
      let unboxInt_l f l =
        f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)  in
      let connectives =
        let _0_474 =
          let _0_462 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
          (FStar_Syntax_Const.and_lid, _0_462)  in
        let _0_473 =
          let _0_472 =
            let _0_463 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
            (FStar_Syntax_Const.or_lid, _0_463)  in
          let _0_471 =
            let _0_470 =
              let _0_469 =
                let _0_464 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)
                   in
                (FStar_Syntax_Const.iff_lid, _0_464)  in
              let _0_468 =
                let _0_467 =
                  let _0_466 =
                    let _0_465 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, _0_465)  in
                  [_0_466;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: _0_467  in
              _0_469 :: _0_468  in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: _0_470  in
          _0_472 :: _0_471  in
        _0_474 :: _0_473  in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____5815 = encode_formula phi' env  in
            (match uu____5815 with
             | (phi,decls) ->
                 let _0_475 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r
                    in
                 (_0_475, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____5822 ->
            let _0_476 = FStar_Syntax_Util.unmeta phi  in
            encode_formula _0_476 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____5855 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____5855 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____5863;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____5865;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____5881 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____5881 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head  in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____5913::(x,uu____5915)::(t,uu____5917)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____5951 = encode_term x env  in
                 (match uu____5951 with
                  | (x,decls) ->
                      let uu____5958 = encode_term t env  in
                      (match uu____5958 with
                       | (t,decls') ->
                           let _0_477 = FStar_SMTEncoding_Term.mk_HasType x t
                              in
                           (_0_477, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____5968)::(msg,uu____5970)::(phi,uu____5972)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6006 =
                   let _0_479 =
                     (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
                      in
                   let _0_478 =
                     (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
                      in
                   (_0_479, _0_478)  in
                 (match uu____6006 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6013))) ->
                      let phi =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r
                         in
                      fallback phi
                  | uu____6029 -> fallback phi)
             | uu____6032 when head_redex env head ->
                 let _0_480 = whnf env phi  in encode_formula _0_480 env
             | uu____6040 ->
                 let uu____6048 = encode_term phi env  in
                 (match uu____6048 with
                  | (tt,decls) ->
                      let _0_481 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___148_6055 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___148_6055.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___148_6055.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (_0_481, decls)))
        | uu____6058 ->
            let uu____6059 = encode_term phi env  in
            (match uu____6059 with
             | (tt,decls) ->
                 let _0_482 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___149_6066 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___149_6066.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___149_6066.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (_0_482, decls))
         in
      let encode_q_body env bs ps body =
        let uu____6093 = encode_binders None bs env  in
        match uu____6093 with
        | (vars,guards,env,decls,uu____6115) ->
            let uu____6122 =
              let _0_484 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6157 =
                          let _0_483 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6179  ->
                                    match uu____6179 with
                                    | (t,uu____6185) ->
                                        encode_term t
                                          (let uu___150_6186 = env  in
                                           {
                                             bindings =
                                               (uu___150_6186.bindings);
                                             depth = (uu___150_6186.depth);
                                             tcenv = (uu___150_6186.tcenv);
                                             warn = (uu___150_6186.warn);
                                             cache = (uu___150_6186.cache);
                                             nolabels =
                                               (uu___150_6186.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___150_6186.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right _0_483 FStar_List.unzip  in
                        match uu____6157 with
                        | (p,decls) -> (p, (FStar_List.flatten decls))))
                 in
              FStar_All.pipe_right _0_484 FStar_List.unzip  in
            (match uu____6122 with
             | (pats,decls') ->
                 let uu____6220 = encode_formula body env  in
                 (match uu____6220 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6239;
                             FStar_SMTEncoding_Term.rng = uu____6240;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6248 -> guards  in
                      let _0_485 = FStar_SMTEncoding_Util.mk_and_l guards  in
                      (vars, pats, _0_485, body,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug phi;
      (let phi = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6284  ->
                   match uu____6284 with
                   | (x,uu____6288) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats with
         | [] -> ()
         | hd::tl ->
             let pat_vars =
               let _0_487 = FStar_Syntax_Free.names hd  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let _0_486 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out _0_486) _0_487 tl
                in
             let uu____6298 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6310  ->
                       match uu____6310 with
                       | (b,uu____6314) ->
                           Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
                in
             (match uu____6298 with
              | None  -> ()
              | Some (x,uu____6318) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl
                     in
                  let _0_489 =
                    let _0_488 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      _0_488
                     in
                  FStar_Errors.warn pos _0_489)
          in
       let uu____6328 = FStar_Syntax_Util.destruct_typ_as_formula phi  in
       match uu____6328 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6334 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____6370  ->
                     match uu____6370 with
                     | (l,uu____6380) -> FStar_Ident.lid_equals op l))
              in
           (match uu____6334 with
            | None  -> fallback phi
            | Some (uu____6403,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6432 = encode_q_body env vars pats body  in
             match uu____6432 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let _0_491 =
                     let _0_490 = FStar_SMTEncoding_Util.mkImp (guard, body)
                        in
                     (pats, vars, _0_490)  in
                   FStar_SMTEncoding_Term.mkForall _0_491
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6469 = encode_q_body env vars pats body  in
             match uu____6469 with
             | (vars,pats,guard,body,decls) ->
                 let _0_494 =
                   let _0_493 =
                     let _0_492 = FStar_SMTEncoding_Util.mkAnd (guard, body)
                        in
                     (pats, vars, _0_492)  in
                   FStar_SMTEncoding_Term.mkExists _0_493
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (_0_494, decls))))

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
  let uu____6542 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____6542 with
  | (asym,a) ->
      let uu____6547 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____6547 with
       | (xsym,x) ->
           let uu____6552 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____6552 with
            | (ysym,y) ->
                let quant vars body x =
                  let xname_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_495 =
                         FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                          in
                       (x, _0_495, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  let xtok = Prims.strcat x "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    FStar_SMTEncoding_Util.mkApp
                      (let _0_496 =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                          in
                       (x, _0_496))
                     in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok vars  in
                  let _0_506 =
                    let _0_505 =
                      let _0_504 =
                        let _0_503 =
                          FStar_SMTEncoding_Term.Assume
                            (let _0_498 =
                               FStar_SMTEncoding_Util.mkForall
                                 (let _0_497 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, _0_497))
                                in
                             (_0_498, None,
                               (Some (Prims.strcat "primitive_" x))))
                           in
                        let _0_502 =
                          let _0_501 =
                            FStar_SMTEncoding_Term.Assume
                              (let _0_500 =
                                 FStar_SMTEncoding_Util.mkForall
                                   (let _0_499 =
                                      FStar_SMTEncoding_Util.mkEq
                                        (xtok_app, xapp)
                                       in
                                    ([[xtok_app]], vars, _0_499))
                                  in
                               (_0_500, (Some "Name-token correspondence"),
                                 (Some
                                    (Prims.strcat "token_correspondence_" x))))
                             in
                          [_0_501]  in
                        _0_503 :: _0_502  in
                      xtok_decl :: _0_504  in
                    xname_decl :: _0_505  in
                  (xtok, _0_506)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims =
                  let _0_602 =
                    let _0_509 =
                      let _0_508 =
                        let _0_507 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          _0_507
                         in
                      quant axy _0_508  in
                    (FStar_Syntax_Const.op_Eq, _0_509)  in
                  let _0_601 =
                    let _0_600 =
                      let _0_512 =
                        let _0_511 =
                          let _0_510 =
                            FStar_SMTEncoding_Util.mkNot
                              (FStar_SMTEncoding_Util.mkEq (x, y))
                             in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            _0_510
                           in
                        quant axy _0_511  in
                      (FStar_Syntax_Const.op_notEq, _0_512)  in
                    let _0_599 =
                      let _0_598 =
                        let _0_517 =
                          let _0_516 =
                            let _0_515 =
                              FStar_SMTEncoding_Util.mkLT
                                (let _0_514 =
                                   FStar_SMTEncoding_Term.unboxInt x  in
                                 let _0_513 =
                                   FStar_SMTEncoding_Term.unboxInt y  in
                                 (_0_514, _0_513))
                               in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool _0_515
                             in
                          quant xy _0_516  in
                        (FStar_Syntax_Const.op_LT, _0_517)  in
                      let _0_597 =
                        let _0_596 =
                          let _0_522 =
                            let _0_521 =
                              let _0_520 =
                                FStar_SMTEncoding_Util.mkLTE
                                  (let _0_519 =
                                     FStar_SMTEncoding_Term.unboxInt x  in
                                   let _0_518 =
                                     FStar_SMTEncoding_Term.unboxInt y  in
                                   (_0_519, _0_518))
                                 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool _0_520
                               in
                            quant xy _0_521  in
                          (FStar_Syntax_Const.op_LTE, _0_522)  in
                        let _0_595 =
                          let _0_594 =
                            let _0_527 =
                              let _0_526 =
                                let _0_525 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_524 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_523 =
                                       FStar_SMTEncoding_Term.unboxInt y  in
                                     (_0_524, _0_523))
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool _0_525
                                 in
                              quant xy _0_526  in
                            (FStar_Syntax_Const.op_GT, _0_527)  in
                          let _0_593 =
                            let _0_592 =
                              let _0_532 =
                                let _0_531 =
                                  let _0_530 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_529 =
                                         FStar_SMTEncoding_Term.unboxInt x
                                          in
                                       let _0_528 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       (_0_529, _0_528))
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool _0_530
                                   in
                                quant xy _0_531  in
                              (FStar_Syntax_Const.op_GTE, _0_532)  in
                            let _0_591 =
                              let _0_590 =
                                let _0_537 =
                                  let _0_536 =
                                    let _0_535 =
                                      FStar_SMTEncoding_Util.mkSub
                                        (let _0_534 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         let _0_533 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         (_0_534, _0_533))
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt _0_535
                                     in
                                  quant xy _0_536  in
                                (FStar_Syntax_Const.op_Subtraction, _0_537)
                                 in
                              let _0_589 =
                                let _0_588 =
                                  let _0_540 =
                                    let _0_539 =
                                      let _0_538 =
                                        FStar_SMTEncoding_Util.mkMinus
                                          (FStar_SMTEncoding_Term.unboxInt x)
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt _0_538
                                       in
                                    quant qx _0_539  in
                                  (FStar_Syntax_Const.op_Minus, _0_540)  in
                                let _0_587 =
                                  let _0_586 =
                                    let _0_545 =
                                      let _0_544 =
                                        let _0_543 =
                                          FStar_SMTEncoding_Util.mkAdd
                                            (let _0_542 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 x
                                                in
                                             let _0_541 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 y
                                                in
                                             (_0_542, _0_541))
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          _0_543
                                         in
                                      quant xy _0_544  in
                                    (FStar_Syntax_Const.op_Addition, _0_545)
                                     in
                                  let _0_585 =
                                    let _0_584 =
                                      let _0_550 =
                                        let _0_549 =
                                          let _0_548 =
                                            FStar_SMTEncoding_Util.mkMul
                                              (let _0_547 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   x
                                                  in
                                               let _0_546 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   y
                                                  in
                                               (_0_547, _0_546))
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            _0_548
                                           in
                                        quant xy _0_549  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        _0_550)
                                       in
                                    let _0_583 =
                                      let _0_582 =
                                        let _0_555 =
                                          let _0_554 =
                                            let _0_553 =
                                              FStar_SMTEncoding_Util.mkDiv
                                                (let _0_552 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     x
                                                    in
                                                 let _0_551 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     y
                                                    in
                                                 (_0_552, _0_551))
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              _0_553
                                             in
                                          quant xy _0_554  in
                                        (FStar_Syntax_Const.op_Division,
                                          _0_555)
                                         in
                                      let _0_581 =
                                        let _0_580 =
                                          let _0_560 =
                                            let _0_559 =
                                              let _0_558 =
                                                FStar_SMTEncoding_Util.mkMod
                                                  (let _0_557 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       x
                                                      in
                                                   let _0_556 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       y
                                                      in
                                                   (_0_557, _0_556))
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                _0_558
                                               in
                                            quant xy _0_559  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            _0_560)
                                           in
                                        let _0_579 =
                                          let _0_578 =
                                            let _0_565 =
                                              let _0_564 =
                                                let _0_563 =
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    (let _0_562 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         x
                                                        in
                                                     let _0_561 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         y
                                                        in
                                                     (_0_562, _0_561))
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  _0_563
                                                 in
                                              quant xy _0_564  in
                                            (FStar_Syntax_Const.op_And,
                                              _0_565)
                                             in
                                          let _0_577 =
                                            let _0_576 =
                                              let _0_570 =
                                                let _0_569 =
                                                  let _0_568 =
                                                    FStar_SMTEncoding_Util.mkOr
                                                      (let _0_567 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           x
                                                          in
                                                       let _0_566 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           y
                                                          in
                                                       (_0_567, _0_566))
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    _0_568
                                                   in
                                                quant xy _0_569  in
                                              (FStar_Syntax_Const.op_Or,
                                                _0_570)
                                               in
                                            let _0_575 =
                                              let _0_574 =
                                                let _0_573 =
                                                  let _0_572 =
                                                    let _0_571 =
                                                      FStar_SMTEncoding_Util.mkNot
                                                        (FStar_SMTEncoding_Term.unboxBool
                                                           x)
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      _0_571
                                                     in
                                                  quant qx _0_572  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  _0_573)
                                                 in
                                              [_0_574]  in
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
                    _0_600 :: _0_599  in
                  _0_602 :: _0_601  in
                let mk l v =
                  let _0_604 =
                    let _0_603 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____6898  ->
                              match uu____6898 with
                              | (l',uu____6907) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right _0_603
                      (FStar_Option.map
                         (fun uu____6928  ->
                            match uu____6928 with | (uu____6939,b) -> b v))
                     in
                  FStar_All.pipe_right _0_604 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____6973  ->
                          match uu____6973 with
                          | (l',uu____6982) -> FStar_Ident.lid_equals l l'))
                   in
                { mk; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____7005 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____7005 with
      | (xxsym,xx) ->
          let uu____7010 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____7010 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               FStar_SMTEncoding_Term.Assume
                 (let _0_610 =
                    FStar_SMTEncoding_Util.mkForall
                      (let _0_607 =
                         FStar_SMTEncoding_Util.mkImp
                           (let _0_606 =
                              FStar_SMTEncoding_Util.mkEq
                                (let _0_605 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, _0_605))
                               in
                            (xx_has_type, _0_606))
                          in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         _0_607))
                     in
                  let _0_609 =
                    Some
                      (varops.mk_unique
                         (let _0_608 = FStar_Util.digest_of_string tapp_hash
                             in
                          Prims.strcat "pretyping_" _0_608))
                     in
                  (_0_610, (Some "pretyping"), _0_609)))
  
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
    let _0_617 =
      FStar_SMTEncoding_Term.Assume
        (let _0_611 =
           FStar_SMTEncoding_Term.mk_HasType
             FStar_SMTEncoding_Term.mk_Term_unit tt
            in
         (_0_611, (Some "unit typing"), (Some "unit_typing")))
       in
    let _0_616 =
      let _0_615 =
        FStar_SMTEncoding_Term.Assume
          (let _0_614 =
             mkForall_fuel
               (let _0_613 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_612 =
                       FStar_SMTEncoding_Util.mkEq
                         (x, FStar_SMTEncoding_Term.mk_Term_unit)
                        in
                     (typing_pred, _0_612))
                   in
                ([[typing_pred]], [xx], _0_613))
              in
           (_0_614, (Some "unit inversion"), (Some "unit_inversion")))
         in
      [_0_615]  in
    _0_617 :: _0_616  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_629 =
      FStar_SMTEncoding_Term.Assume
        (let _0_623 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_622 =
                let _0_619 =
                  let _0_618 = FStar_SMTEncoding_Term.boxBool b  in [_0_618]
                   in
                [_0_619]  in
              let _0_621 =
                let _0_620 = FStar_SMTEncoding_Term.boxBool b  in
                FStar_SMTEncoding_Term.mk_HasType _0_620 tt  in
              (_0_622, [bb], _0_621))
            in
         (_0_623, (Some "bool typing"), (Some "bool_typing")))
       in
    let _0_628 =
      let _0_627 =
        FStar_SMTEncoding_Term.Assume
          (let _0_626 =
             mkForall_fuel
               (let _0_625 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_624 =
                       FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                     (typing_pred, _0_624))
                   in
                ([[typing_pred]], [xx], _0_625))
              in
           (_0_626, (Some "bool inversion"), (Some "bool_inversion")))
         in
      [_0_627]  in
    _0_629 :: _0_628  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let _0_636 =
        FStar_SMTEncoding_Util.mkApp
          (let _0_635 =
             let _0_634 =
               let _0_633 =
                 let _0_632 = FStar_SMTEncoding_Term.boxInt a  in
                 let _0_631 =
                   let _0_630 = FStar_SMTEncoding_Term.boxInt b  in [_0_630]
                    in
                 _0_632 :: _0_631  in
               tt :: _0_633  in
             tt :: _0_634  in
           ("Prims.Precedes", _0_635))
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_636  in
    let precedes_y_x =
      let _0_637 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_637  in
    let _0_667 =
      FStar_SMTEncoding_Term.Assume
        (let _0_643 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_642 =
                let _0_639 =
                  let _0_638 = FStar_SMTEncoding_Term.boxInt b  in [_0_638]
                   in
                [_0_639]  in
              let _0_641 =
                let _0_640 = FStar_SMTEncoding_Term.boxInt b  in
                FStar_SMTEncoding_Term.mk_HasType _0_640 tt  in
              (_0_642, [bb], _0_641))
            in
         (_0_643, (Some "int typing"), (Some "int_typing")))
       in
    let _0_666 =
      let _0_665 =
        FStar_SMTEncoding_Term.Assume
          (let _0_646 =
             mkForall_fuel
               (let _0_645 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_644 = FStar_SMTEncoding_Term.mk_tester "BoxInt" x
                        in
                     (typing_pred, _0_644))
                   in
                ([[typing_pred]], [xx], _0_645))
              in
           (_0_646, (Some "int inversion"), (Some "int_inversion")))
         in
      let _0_664 =
        let _0_663 =
          FStar_SMTEncoding_Term.Assume
            (let _0_662 =
               mkForall_fuel
                 (let _0_661 =
                    FStar_SMTEncoding_Util.mkImp
                      (let _0_660 =
                         FStar_SMTEncoding_Util.mk_and_l
                           (let _0_659 =
                              let _0_658 =
                                let _0_657 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_648 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_647 =
                                       FStar_SMTEncoding_Util.mkInteger'
                                         (Prims.parse_int "0")
                                        in
                                     (_0_648, _0_647))
                                   in
                                let _0_656 =
                                  let _0_655 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_650 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       let _0_649 =
                                         FStar_SMTEncoding_Util.mkInteger'
                                           (Prims.parse_int "0")
                                          in
                                       (_0_650, _0_649))
                                     in
                                  let _0_654 =
                                    let _0_653 =
                                      FStar_SMTEncoding_Util.mkLT
                                        (let _0_652 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         let _0_651 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         (_0_652, _0_651))
                                       in
                                    [_0_653]  in
                                  _0_655 :: _0_654  in
                                _0_657 :: _0_656  in
                              typing_pred_y :: _0_658  in
                            typing_pred :: _0_659)
                          in
                       (_0_660, precedes_y_x))
                     in
                  ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                    _0_661))
                in
             (_0_662, (Some "well-founded ordering on nat (alt)"),
               (Some "well-founded-ordering-on-nat")))
           in
        [_0_663]  in
      _0_665 :: _0_664  in
    _0_667 :: _0_666  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_679 =
      FStar_SMTEncoding_Term.Assume
        (let _0_673 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_672 =
                let _0_669 =
                  let _0_668 = FStar_SMTEncoding_Term.boxString b  in
                  [_0_668]  in
                [_0_669]  in
              let _0_671 =
                let _0_670 = FStar_SMTEncoding_Term.boxString b  in
                FStar_SMTEncoding_Term.mk_HasType _0_670 tt  in
              (_0_672, [bb], _0_671))
            in
         (_0_673, (Some "string typing"), (Some "string_typing")))
       in
    let _0_678 =
      let _0_677 =
        FStar_SMTEncoding_Term.Assume
          (let _0_676 =
             mkForall_fuel
               (let _0_675 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_674 =
                       FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                     (typing_pred, _0_674))
                   in
                ([[typing_pred]], [xx], _0_675))
              in
           (_0_676, (Some "string inversion"), (Some "string_inversion")))
         in
      [_0_677]  in
    _0_679 :: _0_678  in
  let mk_ref env reft_name uu____7230 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      FStar_SMTEncoding_Util.mkApp
        (let _0_681 =
           let _0_680 = FStar_SMTEncoding_Util.mkFreeV aa  in [_0_680]  in
         (reft_name, _0_681))
       in
    let refb =
      FStar_SMTEncoding_Util.mkApp
        (let _0_683 =
           let _0_682 = FStar_SMTEncoding_Util.mkFreeV bb  in [_0_682]  in
         (reft_name, _0_683))
       in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let _0_696 =
      FStar_SMTEncoding_Term.Assume
        (let _0_686 =
           mkForall_fuel
             (let _0_685 =
                FStar_SMTEncoding_Util.mkImp
                  (let _0_684 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                      in
                   (typing_pred, _0_684))
                 in
              ([[typing_pred]], [xx; aa], _0_685))
            in
         (_0_686, (Some "ref inversion"), (Some "ref_inversion")))
       in
    let _0_695 =
      let _0_694 =
        FStar_SMTEncoding_Term.Assume
          (let _0_693 =
             let _0_692 =
               let _0_691 =
                 FStar_SMTEncoding_Util.mkImp
                   (let _0_690 =
                      FStar_SMTEncoding_Util.mkAnd
                        (typing_pred, typing_pred_b)
                       in
                    let _0_689 =
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_688 = FStar_SMTEncoding_Util.mkFreeV aa  in
                         let _0_687 = FStar_SMTEncoding_Util.mkFreeV bb  in
                         (_0_688, _0_687))
                       in
                    (_0_690, _0_689))
                  in
               ([[typing_pred; typing_pred_b]], [xx; aa; bb], _0_691)  in
             mkForall_fuel' (Prims.parse_int "2") _0_692  in
           (_0_693, (Some "ref typing is injective"),
             (Some "ref_injectivity")))
         in
      [_0_694]  in
    _0_696 :: _0_695  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let _0_698 =
      FStar_SMTEncoding_Term.Assume
        (let _0_697 =
           FStar_SMTEncoding_Util.mkIff
             (FStar_SMTEncoding_Util.mkFalse, valid)
            in
         (_0_697, (Some "False interpretation"), (Some "false_interp")))
       in
    [_0_698]  in
  let mk_and_interp env conj uu____7315 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_700 =
           let _0_699 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
           [_0_699]  in
         ("Valid", _0_700))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_704 =
      FStar_SMTEncoding_Term.Assume
        (let _0_703 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_702 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_701 =
                     FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                   (_0_701, valid))
                 in
              ([[valid]], [aa; bb], _0_702))
            in
         (_0_703, (Some "/\\ interpretation"), (Some "l_and-interp")))
       in
    [_0_704]  in
  let mk_or_interp env disj uu____7355 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_706 =
           let _0_705 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
           [_0_705]  in
         ("Valid", _0_706))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_710 =
      FStar_SMTEncoding_Term.Assume
        (let _0_709 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_708 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_707 =
                     FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                   (_0_707, valid))
                 in
              ([[valid]], [aa; bb], _0_708))
            in
         (_0_709, (Some "\\/ interpretation"), (Some "l_or-interp")))
       in
    [_0_710]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let y = FStar_SMTEncoding_Util.mkFreeV yy  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_712 =
           let _0_711 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y])  in
           [_0_711]  in
         ("Valid", _0_712))
       in
    let _0_716 =
      FStar_SMTEncoding_Term.Assume
        (let _0_715 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_714 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_713 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_713, valid))
                 in
              ([[valid]], [aa; xx; yy], _0_714))
            in
         (_0_715, (Some "Eq2 interpretation"), (Some "eq2-interp")))
       in
    [_0_716]  in
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
        (let _0_718 =
           let _0_717 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y])  in
           [_0_717]  in
         ("Valid", _0_718))
       in
    let _0_722 =
      FStar_SMTEncoding_Term.Assume
        (let _0_721 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_720 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_719 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_719, valid))
                 in
              ([[valid]], [aa; bb; xx; yy], _0_720))
            in
         (_0_721, (Some "Eq3 interpretation"), (Some "eq3-interp")))
       in
    [_0_722]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_724 =
           let _0_723 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
           [_0_723]  in
         ("Valid", _0_724))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_728 =
      FStar_SMTEncoding_Term.Assume
        (let _0_727 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_726 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_725 =
                     FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                   (_0_725, valid))
                 in
              ([[valid]], [aa; bb], _0_726))
            in
         (_0_727, (Some "==> interpretation"), (Some "l_imp-interp")))
       in
    [_0_728]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_730 =
           let _0_729 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
           [_0_729]  in
         ("Valid", _0_730))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_734 =
      FStar_SMTEncoding_Term.Assume
        (let _0_733 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_732 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_731 =
                     FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                   (_0_731, valid))
                 in
              ([[valid]], [aa; bb], _0_732))
            in
         (_0_733, (Some "<==> interpretation"), (Some "l_iff-interp")))
       in
    [_0_734]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_736 =
           let _0_735 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
           [_0_735]  in
         ("Valid", _0_736))
       in
    let not_valid_a =
      let _0_737 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_737  in
    let _0_740 =
      FStar_SMTEncoding_Term.Assume
        (let _0_739 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_738 = FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)
                 in
              ([[valid]], [aa], _0_738))
            in
         (_0_739, (Some "not interpretation"), (Some "l_not-interp")))
       in
    [_0_740]  in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_742 =
           let _0_741 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b])  in
           [_0_741]  in
         ("Valid", _0_742))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_744 =
           let _0_743 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_743]
            in
         ("Valid", _0_744))
       in
    let _0_753 =
      FStar_SMTEncoding_Term.Assume
        (let _0_752 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_751 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_750 =
                     FStar_SMTEncoding_Util.mkForall
                       (let _0_749 =
                          let _0_746 =
                            let _0_745 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_745]  in
                          [_0_746]  in
                        let _0_748 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_747 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_747, valid_b_x))
                           in
                        (_0_749, [xx], _0_748))
                      in
                   (_0_750, valid))
                 in
              ([[valid]], [aa; bb], _0_751))
            in
         (_0_752, (Some "forall interpretation"), (Some "forall-interp")))
       in
    [_0_753]  in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_755 =
           let _0_754 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b])  in
           [_0_754]  in
         ("Valid", _0_755))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_757 =
           let _0_756 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_756]
            in
         ("Valid", _0_757))
       in
    let _0_766 =
      FStar_SMTEncoding_Term.Assume
        (let _0_765 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_764 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_763 =
                     FStar_SMTEncoding_Util.mkExists
                       (let _0_762 =
                          let _0_759 =
                            let _0_758 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_758]  in
                          [_0_759]  in
                        let _0_761 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_760 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_760, valid_b_x))
                           in
                        (_0_762, [xx], _0_761))
                      in
                   (_0_763, valid))
                 in
              ([[valid]], [aa; bb], _0_764))
            in
         (_0_765, (Some "exists interpretation"), (Some "exists-interp")))
       in
    [_0_766]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let _0_769 =
      FStar_SMTEncoding_Term.Assume
        (let _0_768 =
           FStar_SMTEncoding_Term.mk_HasTypeZ
             FStar_SMTEncoding_Term.mk_Range_const range_ty
            in
         let _0_767 = Some (varops.mk_unique "typing_range_const")  in
         (_0_768, (Some "Range_const typing"), _0_767))
       in
    [_0_769]  in
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
    (FStar_Syntax_Const.range_lid, mk_range_interp)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____7968 =
            FStar_Util.find_opt
              (fun uu____7986  ->
                 match uu____7986 with
                 | (l,uu____7996) -> FStar_Ident.lid_equals l t) prims
             in
          match uu____7968 with
          | None  -> []
          | Some (uu____8018,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____8055 = encode_function_type_as_formula None None t env  in
        match uu____8055 with
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
            let uu____8088 =
              (let _0_770 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm  in
               FStar_All.pipe_left Prims.op_Negation _0_770) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            match uu____8088 with
            | true  ->
                let uu____8092 = new_term_constant_and_tok_from_lid env lid
                   in
                (match uu____8092 with
                 | (vname,vtok,env) ->
                     let arg_sorts =
                       let uu____8104 =
                         (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                          in
                       match uu____8104 with
                       | FStar_Syntax_Syntax.Tm_arrow (binders,uu____8107) ->
                           FStar_All.pipe_right binders
                             (FStar_List.map
                                (fun uu____8124  ->
                                   FStar_SMTEncoding_Term.Term_sort))
                       | uu____8127 -> []  in
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
            | uu____8135 ->
                let uu____8136 = prims.is lid  in
                (match uu____8136 with
                 | true  ->
                     let vname = varops.new_fvar lid  in
                     let uu____8141 = prims.mk lid vname  in
                     (match uu____8141 with
                      | (tok,definition) ->
                          let env = push_free_var env lid vname (Some tok)
                             in
                          (definition, env))
                 | uu____8154 ->
                     let encode_non_total_function_typ =
                       lid.FStar_Ident.nsstr <> "Prims"  in
                     let uu____8156 =
                       let uu____8162 = curried_arrow_formals_comp t_norm  in
                       match uu____8162 with
                       | (args,comp) ->
                           (match encode_non_total_function_typ with
                            | true  ->
                                let _0_771 =
                                  FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                    env.tcenv comp
                                   in
                                (args, _0_771)
                            | uu____8180 ->
                                (args,
                                  (None,
                                    (FStar_Syntax_Util.comp_result comp))))
                        in
                     (match uu____8156 with
                      | (formals,(pre_opt,res_t)) ->
                          let uu____8200 =
                            new_term_constant_and_tok_from_lid env lid  in
                          (match uu____8200 with
                           | (vname,vtok,env) ->
                               let vtok_tm =
                                 match formals with
                                 | [] ->
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (vname,
                                         FStar_SMTEncoding_Term.Term_sort)
                                 | uu____8213 ->
                                     FStar_SMTEncoding_Util.mkApp (vtok, [])
                                  in
                               let mk_disc_proj_axioms guard encoded_res_t
                                 vapp vars =
                                 FStar_All.pipe_right quals
                                   (FStar_List.collect
                                      (fun uu___123_8237  ->
                                         match uu___123_8237 with
                                         | FStar_Syntax_Syntax.Discriminator
                                             d ->
                                             let uu____8240 =
                                               FStar_Util.prefix vars  in
                                             (match uu____8240 with
                                              | (uu____8251,(xxsym,uu____8253))
                                                  ->
                                                  let xx =
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                      (xxsym,
                                                        FStar_SMTEncoding_Term.Term_sort)
                                                     in
                                                  let _0_776 =
                                                    FStar_SMTEncoding_Term.Assume
                                                      (let _0_775 =
                                                         FStar_SMTEncoding_Util.mkForall
                                                           (let _0_774 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (let _0_773 =
                                                                   let _0_772
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    (escape
                                                                    d.FStar_Ident.str)
                                                                    xx  in
                                                                   FStar_All.pipe_left
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    _0_772
                                                                    in
                                                                 (vapp,
                                                                   _0_773))
                                                               in
                                                            ([[vapp]], vars,
                                                              _0_774))
                                                          in
                                                       (_0_775,
                                                         (Some
                                                            "Discriminator equation"),
                                                         (Some
                                                            (Prims.strcat
                                                               "disc_equation_"
                                                               (escape
                                                                  d.FStar_Ident.str)))))
                                                     in
                                                  [_0_776])
                                         | FStar_Syntax_Syntax.Projector
                                             (d,f) ->
                                             let uu____8274 =
                                               FStar_Util.prefix vars  in
                                             (match uu____8274 with
                                              | (uu____8285,(xxsym,uu____8287))
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
                                                  let _0_779 =
                                                    FStar_SMTEncoding_Term.Assume
                                                      (let _0_778 =
                                                         FStar_SMTEncoding_Util.mkForall
                                                           (let _0_777 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (vapp,
                                                                  prim_app)
                                                               in
                                                            ([[vapp]], vars,
                                                              _0_777))
                                                          in
                                                       (_0_778,
                                                         (Some
                                                            "Projector equation"),
                                                         (Some
                                                            (Prims.strcat
                                                               "proj_equation_"
                                                               tp_name))))
                                                     in
                                                  [_0_779])
                                         | uu____8310 -> []))
                                  in
                               let uu____8311 =
                                 encode_binders None formals env  in
                               (match uu____8311 with
                                | (vars,guards,env',decls1,uu____8327) ->
                                    let uu____8334 =
                                      match pre_opt with
                                      | None  ->
                                          let _0_780 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              guards
                                             in
                                          (_0_780, decls1)
                                      | Some p ->
                                          let uu____8340 =
                                            encode_formula p env'  in
                                          (match uu____8340 with
                                           | (g,ds) ->
                                               let _0_781 =
                                                 FStar_SMTEncoding_Util.mk_and_l
                                                   (g :: guards)
                                                  in
                                               (_0_781,
                                                 (FStar_List.append decls1 ds)))
                                       in
                                    (match uu____8334 with
                                     | (guard,decls1) ->
                                         let vtok_app = mk_Apply vtok_tm vars
                                            in
                                         let vapp =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_782 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  vars
                                                 in
                                              (vname, _0_782))
                                            in
                                         let uu____8358 =
                                           let vname_decl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (let _0_783 =
                                                  FStar_All.pipe_right
                                                    formals
                                                    (FStar_List.map
                                                       (fun uu____8368  ->
                                                          FStar_SMTEncoding_Term.Term_sort))
                                                   in
                                                (vname, _0_783,
                                                  FStar_SMTEncoding_Term.Term_sort,
                                                  None))
                                              in
                                           let uu____8371 =
                                             let env =
                                               let uu___151_8375 = env  in
                                               {
                                                 bindings =
                                                   (uu___151_8375.bindings);
                                                 depth =
                                                   (uu___151_8375.depth);
                                                 tcenv =
                                                   (uu___151_8375.tcenv);
                                                 warn = (uu___151_8375.warn);
                                                 cache =
                                                   (uu___151_8375.cache);
                                                 nolabels =
                                                   (uu___151_8375.nolabels);
                                                 use_zfuel_name =
                                                   (uu___151_8375.use_zfuel_name);
                                                 encode_non_total_function_typ
                                               }  in
                                             let uu____8376 =
                                               Prims.op_Negation
                                                 (head_normal env tt)
                                                in
                                             match uu____8376 with
                                             | true  ->
                                                 encode_term_pred None tt env
                                                   vtok_tm
                                             | uu____8379 ->
                                                 encode_term_pred None t_norm
                                                   env vtok_tm
                                              in
                                           match uu____8371 with
                                           | (tok_typing,decls2) ->
                                               let tok_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Some
                                                        (Prims.strcat
                                                           "function_token_typing_"
                                                           vname)))
                                                  in
                                               let uu____8388 =
                                                 match formals with
                                                 | [] ->
                                                     let _0_787 =
                                                       let _0_786 =
                                                         let _0_785 =
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                             (vname,
                                                               FStar_SMTEncoding_Term.Term_sort)
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _0_784  ->
                                                              Some _0_784)
                                                           _0_785
                                                          in
                                                       push_free_var env lid
                                                         vname _0_786
                                                        in
                                                     ((FStar_List.append
                                                         decls2 [tok_typing]),
                                                       _0_787)
                                                 | uu____8399 ->
                                                     let vtok_decl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (vtok, [],
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None)
                                                        in
                                                     let vtok_fresh =
                                                       let _0_788 =
                                                         varops.next_id ()
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_token
                                                         (vtok,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                         _0_788
                                                        in
                                                     let name_tok_corr =
                                                       FStar_SMTEncoding_Term.Assume
                                                         (let _0_790 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              (let _0_789 =
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   (vtok_app,
                                                                    vapp)
                                                                  in
                                                               ([[vtok_app];
                                                                [vapp]],
                                                                 vars,
                                                                 _0_789))
                                                             in
                                                          (_0_790,
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
                                               (match uu____8388 with
                                                | (tok_decl,env) ->
                                                    ((vname_decl ::
                                                      tok_decl), env))
                                            in
                                         (match uu____8358 with
                                          | (decls2,env) ->
                                              let uu____8429 =
                                                let res_t =
                                                  FStar_Syntax_Subst.compress
                                                    res_t
                                                   in
                                                let uu____8434 =
                                                  encode_term res_t env'  in
                                                match uu____8434 with
                                                | (encoded_res_t,decls) ->
                                                    let _0_791 =
                                                      FStar_SMTEncoding_Term.mk_HasType
                                                        vapp encoded_res_t
                                                       in
                                                    (encoded_res_t, _0_791,
                                                      decls)
                                                 in
                                              (match uu____8429 with
                                               | (encoded_res_t,ty_pred,decls3)
                                                   ->
                                                   let typingAx =
                                                     FStar_SMTEncoding_Term.Assume
                                                       (let _0_793 =
                                                          FStar_SMTEncoding_Util.mkForall
                                                            (let _0_792 =
                                                               FStar_SMTEncoding_Util.mkImp
                                                                 (guard,
                                                                   ty_pred)
                                                                in
                                                             ([[vapp]], vars,
                                                               _0_792))
                                                           in
                                                        (_0_793,
                                                          (Some
                                                             "free var typing"),
                                                          (Some
                                                             (Prims.strcat
                                                                "typing_"
                                                                vname))))
                                                      in
                                                   let freshness =
                                                     let uu____8458 =
                                                       FStar_All.pipe_right
                                                         quals
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.New)
                                                        in
                                                     match uu____8458 with
                                                     | true  ->
                                                         let _0_798 =
                                                           FStar_SMTEncoding_Term.fresh_constructor
                                                             (let _0_795 =
                                                                FStar_All.pipe_right
                                                                  vars
                                                                  (FStar_List.map
                                                                    Prims.snd)
                                                                 in
                                                              let _0_794 =
                                                                varops.next_id
                                                                  ()
                                                                 in
                                                              (vname, _0_795,
                                                                FStar_SMTEncoding_Term.Term_sort,
                                                                _0_794))
                                                            in
                                                         let _0_797 =
                                                           let _0_796 =
                                                             pretype_axiom
                                                               vapp vars
                                                              in
                                                           [_0_796]  in
                                                         _0_798 :: _0_797
                                                     | uu____8466 -> []  in
                                                   let g =
                                                     let _0_803 =
                                                       let _0_802 =
                                                         let _0_801 =
                                                           let _0_800 =
                                                             let _0_799 =
                                                               mk_disc_proj_axioms
                                                                 guard
                                                                 encoded_res_t
                                                                 vapp vars
                                                                in
                                                             typingAx ::
                                                               _0_799
                                                              in
                                                           FStar_List.append
                                                             freshness _0_800
                                                            in
                                                         FStar_List.append
                                                           decls3 _0_801
                                                          in
                                                       FStar_List.append
                                                         decls2 _0_802
                                                        in
                                                     FStar_List.append decls1
                                                       _0_803
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
          let uu____8489 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8489 with
          | None  ->
              let uu____8512 = encode_free_var env x t t_norm []  in
              (match uu____8512 with
               | (decls,env) ->
                   let uu____8527 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____8527 with
                    | (n,x',uu____8546) -> ((n, x'), decls, env)))
          | Some (n,x,uu____8558) -> ((n, x), [], env)
  
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
          let uu____8591 = encode_free_var env lid t tt quals  in
          match uu____8591 with
          | (decls,env) ->
              let uu____8602 = FStar_Syntax_Util.is_smt_lemma t  in
              (match uu____8602 with
               | true  ->
                   let _0_805 =
                     let _0_804 = encode_smt_lemma env lid tt  in
                     FStar_List.append decls _0_804  in
                   (_0_805, env)
               | uu____8607 -> (decls, env))
  
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
             (fun uu____8632  ->
                fun lb  ->
                  match uu____8632 with
                  | (decls,env) ->
                      let uu____8644 =
                        let _0_806 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env _0_806
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8644 with
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
    fun uu____8671  ->
      fun quals  ->
        match uu____8671 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8720 = FStar_Util.first_N nbinders formals  in
              match uu____8720 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____8760  ->
                         fun uu____8761  ->
                           match (uu____8760, uu____8761) with
                           | ((formal,uu____8771),(binder,uu____8773)) ->
                               FStar_Syntax_Syntax.NT
                                 (let _0_807 =
                                    FStar_Syntax_Syntax.bv_to_name binder  in
                                  (formal, _0_807))) formals binders
                     in
                  let extra_formals =
                    let _0_810 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8798  ->
                              match uu____8798 with
                              | (x,i) ->
                                  let _0_809 =
                                    let uu___152_8805 = x  in
                                    let _0_808 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___152_8805.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___152_8805.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = _0_808
                                    }  in
                                  (_0_809, i)))
                       in
                    FStar_All.pipe_right _0_810
                      FStar_Syntax_Util.name_binders
                     in
                  let body =
                    let _0_816 =
                      let _0_815 =
                        (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
                         in
                      FStar_All.pipe_left (fun _0_814  -> Some _0_814) _0_815
                       in
                    (let _0_813 = FStar_Syntax_Subst.compress body  in
                     let _0_812 =
                       let _0_811 =
                         FStar_Syntax_Util.args_of_binders extra_formals  in
                       FStar_All.pipe_left Prims.snd _0_811  in
                     FStar_Syntax_Syntax.extend_app_n _0_813 _0_812) _0_816
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals), body)
               in
            let destruct_bound_function flid t_norm e =
              let rec aux norm t_norm =
                let uu____8866 = FStar_Syntax_Util.abs_formals e  in
                match uu____8866 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8919::uu____8920 ->
                         let uu____8928 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____8928 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8955 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8955 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = FStar_Syntax_Util.comp_result c
                                      in
                                   let uu____8985 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c)
                                      in
                                   (match uu____8985 with
                                    | true  ->
                                        let uu____9005 =
                                          FStar_Util.first_N nformals binders
                                           in
                                        (match uu____9005 with
                                         | (bs0,rest) ->
                                             let c =
                                               let subst =
                                                 FStar_List.map2
                                                   (fun uu____9053  ->
                                                      fun uu____9054  ->
                                                        match (uu____9053,
                                                                uu____9054)
                                                        with
                                                        | ((x,uu____9064),
                                                           (b,uu____9066)) ->
                                                            FStar_Syntax_Syntax.NT
                                                              (let _0_817 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               (x, _0_817)))
                                                   formals bs0
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
                                    | uu____9092 ->
                                        (match nformals > nbinders with
                                         | true  ->
                                             let uu____9112 =
                                               eta_expand binders formals
                                                 body tres
                                                in
                                             (match uu____9112 with
                                              | (binders,body) ->
                                                  ((binders, body, formals,
                                                     tres), false))
                                         | uu____9164 ->
                                             ((binders, body, formals, tres),
                                               false))))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____9174) ->
                              let _0_818 =
                                Prims.fst
                                  (aux norm x.FStar_Syntax_Syntax.sort)
                                 in
                              (_0_818, true)
                          | uu____9203 when Prims.op_Negation norm ->
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
                          | uu____9205 ->
                              failwith
                                (let _0_820 =
                                   FStar_Syntax_Print.term_to_string e  in
                                 let _0_819 =
                                   FStar_Syntax_Print.term_to_string t_norm
                                    in
                                 FStar_Util.format3
                                   "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                   flid.FStar_Ident.str _0_820 _0_819))
                     | uu____9220 ->
                         let uu____9221 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____9221 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____9248 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____9248 with
                               | (formals,c) ->
                                   let tres = FStar_Syntax_Util.comp_result c
                                      in
                                   let uu____9270 =
                                     eta_expand [] formals e tres  in
                                   (match uu____9270 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____9324 -> (([], e, [], t_norm), false)))
                 in
              aux false t_norm  in
            FStar_All.try_with
              (fun uu___154_9348  ->
                 match () with
                 | () ->
                     let uu____9352 =
                       FStar_All.pipe_right bindings
                         (FStar_Util.for_all
                            (fun lb  ->
                               FStar_Syntax_Util.is_lemma
                                 lb.FStar_Syntax_Syntax.lbtyp))
                        in
                     (match uu____9352 with
                      | true  -> encode_top_level_vals env bindings quals
                      | uu____9358 ->
                          let uu____9359 =
                            FStar_All.pipe_right bindings
                              (FStar_List.fold_left
                                 (fun uu____9400  ->
                                    fun lb  ->
                                      match uu____9400 with
                                      | (toks,typs,decls,env) ->
                                          ((let uu____9451 =
                                              FStar_Syntax_Util.is_lemma
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            match uu____9451 with
                                            | true  ->
                                                Prims.raise
                                                  Let_rec_unencodeable
                                            | uu____9452 -> ());
                                           (let t_norm =
                                              whnf env
                                                lb.FStar_Syntax_Syntax.lbtyp
                                               in
                                            let uu____9454 =
                                              let _0_821 =
                                                FStar_Util.right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                 in
                                              declare_top_level_let env
                                                _0_821
                                                lb.FStar_Syntax_Syntax.lbtyp
                                                t_norm
                                               in
                                            match uu____9454 with
                                            | (tok,decl,env) ->
                                                let _0_824 =
                                                  let _0_823 =
                                                    let _0_822 =
                                                      FStar_Util.right
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    (_0_822, tok)  in
                                                  _0_823 :: toks  in
                                                (_0_824, (t_norm :: typs),
                                                  (decl :: decls), env))))
                                 ([], [], [], env))
                             in
                          (match uu____9359 with
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
                                 | uu____9587 ->
                                     (match curry with
                                      | true  ->
                                          (match ftok with
                                           | Some ftok -> mk_Apply ftok vars
                                           | None  ->
                                               let _0_825 =
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                   (f,
                                                     FStar_SMTEncoding_Term.Term_sort)
                                                  in
                                               mk_Apply _0_825 vars)
                                      | uu____9592 ->
                                          FStar_SMTEncoding_Util.mkApp
                                            (let _0_826 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 vars
                                                in
                                             (f, _0_826)))
                                  in
                               let uu____9596 =
                                 (FStar_All.pipe_right quals
                                    (FStar_Util.for_some
                                       (fun uu___124_9598  ->
                                          match uu___124_9598 with
                                          | FStar_Syntax_Syntax.HasMaskedEffect
                                               -> true
                                          | uu____9599 -> false)))
                                   ||
                                   (FStar_All.pipe_right typs
                                      (FStar_Util.for_some
                                         (fun t  ->
                                            let _0_827 =
                                              FStar_Syntax_Util.is_pure_or_ghost_function
                                                t
                                               in
                                            FStar_All.pipe_left
                                              Prims.op_Negation _0_827)))
                                  in
                               (match uu____9596 with
                                | true  -> (decls, env)
                                | uu____9606 ->
                                    (match Prims.op_Negation is_rec with
                                     | true  ->
                                         (match (bindings, typs, toks) with
                                          | ({
                                               FStar_Syntax_Syntax.lbname =
                                                 uu____9621;
                                               FStar_Syntax_Syntax.lbunivs =
                                                 uu____9622;
                                               FStar_Syntax_Syntax.lbtyp =
                                                 uu____9623;
                                               FStar_Syntax_Syntax.lbeff =
                                                 uu____9624;
                                               FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                                             (flid_fv,(f,ftok))::[]) ->
                                              let e =
                                                FStar_Syntax_Subst.compress e
                                                 in
                                              let flid =
                                                (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                 in
                                              let uu____9666 =
                                                destruct_bound_function flid
                                                  t_norm e
                                                 in
                                              (match uu____9666 with
                                               | ((binders,body,uu____9678,uu____9679),curry)
                                                   ->
                                                   ((let uu____9686 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env.tcenv)
                                                         (FStar_Options.Other
                                                            "SMTEncoding")
                                                        in
                                                     match uu____9686 with
                                                     | true  ->
                                                         let _0_829 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", " binders
                                                            in
                                                         let _0_828 =
                                                           FStar_Syntax_Print.term_to_string
                                                             body
                                                            in
                                                         FStar_Util.print2
                                                           "Encoding let : binders=[%s], body=%s\n"
                                                           _0_829 _0_828
                                                     | uu____9687 -> ());
                                                    (let uu____9688 =
                                                       encode_binders None
                                                         binders env
                                                        in
                                                     match uu____9688 with
                                                     | (vars,guards,env',binder_decls,uu____9704)
                                                         ->
                                                         let app =
                                                           mk_app curry f
                                                             ftok vars
                                                            in
                                                         let uu____9712 =
                                                           let uu____9717 =
                                                             FStar_All.pipe_right
                                                               quals
                                                               (FStar_List.contains
                                                                  FStar_Syntax_Syntax.Logic)
                                                              in
                                                           match uu____9717
                                                           with
                                                           | true  ->
                                                               let _0_831 =
                                                                 FStar_SMTEncoding_Term.mk_Valid
                                                                   app
                                                                  in
                                                               let _0_830 =
                                                                 encode_formula
                                                                   body env'
                                                                  in
                                                               (_0_831,
                                                                 _0_830)
                                                           | uu____9725 ->
                                                               let _0_832 =
                                                                 encode_term
                                                                   body env'
                                                                  in
                                                               (app, _0_832)
                                                            in
                                                         (match uu____9712
                                                          with
                                                          | (app,(body,decls2))
                                                              ->
                                                              let eqn =
                                                                FStar_SMTEncoding_Term.Assume
                                                                  (let _0_835
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_833
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    body)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_833))
                                                                     in
                                                                   let _0_834
                                                                    =
                                                                    Some
                                                                    (FStar_Util.format1
                                                                    "Equation for %s"
                                                                    flid.FStar_Ident.str)
                                                                     in
                                                                   (_0_835,
                                                                    _0_834,
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equation_"
                                                                    f))))
                                                                 in
                                                              let _0_840 =
                                                                let _0_839 =
                                                                  let _0_838
                                                                    =
                                                                    let _0_837
                                                                    =
                                                                    let _0_836
                                                                    =
                                                                    primitive_type_axioms
                                                                    env.tcenv
                                                                    flid f
                                                                    app  in
                                                                    FStar_List.append
                                                                    [eqn]
                                                                    _0_836
                                                                     in
                                                                    FStar_List.append
                                                                    decls2
                                                                    _0_837
                                                                     in
                                                                  FStar_List.append
                                                                    binder_decls
                                                                    _0_838
                                                                   in
                                                                FStar_List.append
                                                                  decls
                                                                  _0_839
                                                                 in
                                                              (_0_840, env)))))
                                          | uu____9745 ->
                                              failwith "Impossible")
                                     | uu____9760 ->
                                         let fuel =
                                           let _0_841 = varops.fresh "fuel"
                                              in
                                           (_0_841,
                                             FStar_SMTEncoding_Term.Fuel_sort)
                                            in
                                         let fuel_tm =
                                           FStar_SMTEncoding_Util.mkFreeV
                                             fuel
                                            in
                                         let env0 = env  in
                                         let uu____9766 =
                                           FStar_All.pipe_right toks
                                             (FStar_List.fold_left
                                                (fun uu____9805  ->
                                                   fun uu____9806  ->
                                                     match (uu____9805,
                                                             uu____9806)
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
                                                           let _0_844 =
                                                             let _0_843 =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 (g,
                                                                   [fuel_tm])
                                                                in
                                                             FStar_All.pipe_left
                                                               (fun _0_842 
                                                                  ->
                                                                  Some _0_842)
                                                               _0_843
                                                              in
                                                           push_free_var env
                                                             flid gtok _0_844
                                                            in
                                                         (((flid, f, ftok, g,
                                                             gtok) :: gtoks),
                                                           env)) ([], env))
                                            in
                                         (match uu____9766 with
                                          | (gtoks,env) ->
                                              let gtoks =
                                                FStar_List.rev gtoks  in
                                              let encode_one_binding env0
                                                uu____9973 t_norm uu____9975
                                                =
                                                match (uu____9973,
                                                        uu____9975)
                                                with
                                                | ((flid,f,ftok,g,gtok),
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = lbn;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uu____9999;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = uu____10000;
                                                     FStar_Syntax_Syntax.lbeff
                                                       = uu____10001;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = e;_})
                                                    ->
                                                    ((let uu____10019 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env0.tcenv)
                                                          (FStar_Options.Other
                                                             "SMTEncoding")
                                                         in
                                                      match uu____10019 with
                                                      | true  ->
                                                          let _0_847 =
                                                            FStar_Syntax_Print.lbname_to_string
                                                              lbn
                                                             in
                                                          let _0_846 =
                                                            FStar_Syntax_Print.term_to_string
                                                              t_norm
                                                             in
                                                          let _0_845 =
                                                            FStar_Syntax_Print.term_to_string
                                                              e
                                                             in
                                                          FStar_Util.print3
                                                            "Encoding let rec %s : %s = %s\n"
                                                            _0_847 _0_846
                                                            _0_845
                                                      | uu____10020 -> ());
                                                     (let uu____10021 =
                                                        destruct_bound_function
                                                          flid t_norm e
                                                         in
                                                      match uu____10021 with
                                                      | ((binders,body,formals,tres),curry)
                                                          ->
                                                          ((let uu____10043 =
                                                              FStar_All.pipe_left
                                                                (FStar_TypeChecker_Env.debug
                                                                   env0.tcenv)
                                                                (FStar_Options.Other
                                                                   "SMTEncoding")
                                                               in
                                                            match uu____10043
                                                            with
                                                            | true  ->
                                                                let _0_851 =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    binders
                                                                   in
                                                                let _0_850 =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    body
                                                                   in
                                                                let _0_849 =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    formals
                                                                   in
                                                                let _0_848 =
                                                                  FStar_Syntax_Print.term_to_string
                                                                    tres
                                                                   in
                                                                FStar_Util.print4
                                                                  "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                                  _0_851
                                                                  _0_850
                                                                  _0_849
                                                                  _0_848
                                                            | uu____10044 ->
                                                                ());
                                                           (match curry with
                                                            | true  ->
                                                                failwith
                                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                            | uu____10046 ->
                                                                ());
                                                           (let uu____10047 =
                                                              encode_binders
                                                                None binders
                                                                env
                                                               in
                                                            match uu____10047
                                                            with
                                                            | (vars,guards,env',binder_decls,uu____10065)
                                                                ->
                                                                let decl_g =
                                                                  FStar_SMTEncoding_Term.DeclFun
                                                                    (
                                                                    let _0_853
                                                                    =
                                                                    let _0_852
                                                                    =
                                                                    FStar_List.map
                                                                    Prims.snd
                                                                    vars  in
                                                                    FStar_SMTEncoding_Term.Fuel_sort
                                                                    :: _0_852
                                                                     in
                                                                    (g,
                                                                    _0_853,
                                                                    FStar_SMTEncoding_Term.Term_sort,
                                                                    (Some
                                                                    "Fuel-instrumented function name")))
                                                                   in
                                                                let env0 =
                                                                  push_zfuel_name
                                                                    env0 flid
                                                                    g
                                                                   in
                                                                let decl_g_tok
                                                                  =
                                                                  FStar_SMTEncoding_Term.DeclFun
                                                                    (gtok,
                                                                    [],
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
                                                                    (
                                                                    let _0_854
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                    (f,
                                                                    _0_854))
                                                                   in
                                                                let gsapp =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    (
                                                                    let _0_856
                                                                    =
                                                                    let _0_855
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm])
                                                                     in
                                                                    _0_855 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_856))
                                                                   in
                                                                let gmax =
                                                                  FStar_SMTEncoding_Util.mkApp
                                                                    (
                                                                    let _0_858
                                                                    =
                                                                    let _0_857
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    [])  in
                                                                    _0_857 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_858))
                                                                   in
                                                                let uu____10095
                                                                  =
                                                                  encode_term
                                                                    body env'
                                                                   in
                                                                (match uu____10095
                                                                 with
                                                                 | (body_tm,decls2)
                                                                    ->
                                                                    let eqn_g
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_861
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall'
                                                                    (let _0_859
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
                                                                    _0_859))
                                                                     in
                                                                    let _0_860
                                                                    =
                                                                    Some
                                                                    (FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str)
                                                                     in
                                                                    (_0_861,
                                                                    _0_860,
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))))  in
                                                                    let eqn_f
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_863
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_862
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_862))
                                                                     in
                                                                    (_0_863,
                                                                    (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))))  in
                                                                    let eqn_g'
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_868
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_867
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (let _0_866
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (let _0_865
                                                                    =
                                                                    let _0_864
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    _0_864 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_865))
                                                                     in
                                                                    (gsapp,
                                                                    _0_866))
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_867))
                                                                     in
                                                                    (_0_868,
                                                                    (Some
                                                                    "Fuel irrelevance"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))))  in
                                                                    let uu____10139
                                                                    =
                                                                    let uu____10144
                                                                    =
                                                                    encode_binders
                                                                    None
                                                                    formals
                                                                    env0  in
                                                                    match uu____10144
                                                                    with
                                                                    | 
                                                                    (vars,v_guards,env,binder_decls,uu____10161)
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
                                                                    let _0_869
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    _0_869
                                                                    (fuel ::
                                                                    vars)  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_871
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_870))
                                                                     in
                                                                    (_0_871,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))))
                                                                     in
                                                                    let uu____10189
                                                                    =
                                                                    let uu____10193
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env gapp
                                                                     in
                                                                    match uu____10193
                                                                    with
                                                                    | 
                                                                    (g_typing,d3)
                                                                    ->
                                                                    let _0_876
                                                                    =
                                                                    let _0_875
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_873
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_872
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (_0_872,
                                                                    g_typing))
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_873))
                                                                     in
                                                                    (_0_874,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))))  in
                                                                    [_0_875]
                                                                     in
                                                                    (d3,
                                                                    _0_876)
                                                                     in
                                                                    (match uu____10189
                                                                    with
                                                                    | 
                                                                    (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                                     in
                                                                    (match uu____10139
                                                                    with
                                                                    | 
                                                                    (aux_decls,g_typing)
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
                                                                    env0)))))))
                                                 in
                                              let uu____10236 =
                                                let _0_877 =
                                                  FStar_List.zip3 gtoks typs
                                                    bindings
                                                   in
                                                FStar_List.fold_left
                                                  (fun uu____10258  ->
                                                     fun uu____10259  ->
                                                       match (uu____10258,
                                                               uu____10259)
                                                       with
                                                       | ((decls,eqns,env0),
                                                          (gtok,ty,lb)) ->
                                                           let uu____10335 =
                                                             encode_one_binding
                                                               env0 gtok ty
                                                               lb
                                                              in
                                                           (match uu____10335
                                                            with
                                                            | (decls',eqns',env0)
                                                                ->
                                                                ((decls' ::
                                                                  decls),
                                                                  (FStar_List.append
                                                                    eqns'
                                                                    eqns),
                                                                  env0)))
                                                  ([decls], [], env0) _0_877
                                                 in
                                              (match uu____10236 with
                                               | (decls,eqns,env0) ->
                                                   let uu____10381 =
                                                     let _0_878 =
                                                       FStar_All.pipe_right
                                                         decls
                                                         FStar_List.flatten
                                                        in
                                                     FStar_All.pipe_right
                                                       _0_878
                                                       (FStar_List.partition
                                                          (fun uu___125_10394
                                                              ->
                                                             match uu___125_10394
                                                             with
                                                             | FStar_SMTEncoding_Term.DeclFun
                                                                 uu____10395
                                                                 -> true
                                                             | uu____10401 ->
                                                                 false))
                                                      in
                                                   (match uu____10381 with
                                                    | (prefix_decls,rest) ->
                                                        let eqns =
                                                          FStar_List.rev eqns
                                                           in
                                                        ((FStar_List.append
                                                            prefix_decls
                                                            (FStar_List.append
                                                               rest eqns)),
                                                          env0)))))))))
              (fun uu___153_10414  ->
                 match uu___153_10414 with
                 | Let_rec_unencodeable  ->
                     let msg =
                       let _0_879 =
                         FStar_All.pipe_right bindings
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Syntax_Print.lbname_to_string
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       FStar_All.pipe_right _0_879
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
      (let uu____10450 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       match uu____10450 with
       | true  ->
           let _0_880 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n")
             _0_880
       | uu____10451 -> ());
      (let nm =
         let uu____10453 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____10453 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____10456 = encode_sigelt' env se  in
       match uu____10456 with
       | (g,e) ->
           (match g with
            | [] ->
                let _0_882 =
                  let _0_881 =
                    FStar_SMTEncoding_Term.Caption
                      (FStar_Util.format1 "<Skipped %s/>" nm)
                     in
                  [_0_881]  in
                (_0_882, e)
            | uu____10466 ->
                let _0_887 =
                  let _0_886 =
                    let _0_883 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "<Start encoding %s>" nm)
                       in
                    _0_883 :: g  in
                  let _0_885 =
                    let _0_884 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "</end encoding %s>" nm)
                       in
                    [_0_884]  in
                  FStar_List.append _0_886 _0_885  in
                (_0_887, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10474 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____10485) ->
          let uu____10486 =
            let _0_888 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right _0_888 Prims.op_Negation  in
          (match uu____10486 with
           | true  -> ([], env)
           | uu____10491 ->
               let close_effect_params tm =
                 match ed.FStar_Syntax_Syntax.binders with
                 | [] -> tm
                 | uu____10506 ->
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (let _0_890 =
                              FStar_All.pipe_left
                                (fun _0_889  -> Some _0_889)
                                (FStar_Util.Inr
                                   (FStar_Syntax_Const.effect_Tot_lid,
                                     [FStar_Syntax_Syntax.TOTAL]))
                               in
                            ((ed.FStar_Syntax_Syntax.binders), tm, _0_890))))
                       None tm.FStar_Syntax_Syntax.pos
                  in
               let encode_action env a =
                 let uu____10553 =
                   new_term_constant_and_tok_from_lid env
                     a.FStar_Syntax_Syntax.action_name
                    in
                 match uu____10553 with
                 | (aname,atok,env) ->
                     let uu____10563 =
                       FStar_Syntax_Util.arrow_formals_comp
                         a.FStar_Syntax_Syntax.action_typ
                        in
                     (match uu____10563 with
                      | (formals,uu____10573) ->
                          let uu____10580 =
                            let _0_891 =
                              close_effect_params
                                a.FStar_Syntax_Syntax.action_defn
                               in
                            encode_term _0_891 env  in
                          (match uu____10580 with
                           | (tm,decls) ->
                               let a_decls =
                                 let _0_893 =
                                   FStar_SMTEncoding_Term.DeclFun
                                     (let _0_892 =
                                        FStar_All.pipe_right formals
                                          (FStar_List.map
                                             (fun uu____10598  ->
                                                FStar_SMTEncoding_Term.Term_sort))
                                         in
                                      (aname, _0_892,
                                        FStar_SMTEncoding_Term.Term_sort,
                                        (Some "Action")))
                                    in
                                 [_0_893;
                                 FStar_SMTEncoding_Term.DeclFun
                                   (atok, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action token"))]
                                  in
                               let uu____10603 =
                                 let aux uu____10632 uu____10633 =
                                   match (uu____10632, uu____10633) with
                                   | ((bv,uu____10660),(env,acc_sorts,acc))
                                       ->
                                       let uu____10681 = gen_term_var env bv
                                          in
                                       (match uu____10681 with
                                        | (xxsym,xx,env) ->
                                            (env,
                                              ((xxsym,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              :: acc_sorts), (xx :: acc)))
                                    in
                                 FStar_List.fold_right aux formals
                                   (env, [], [])
                                  in
                               (match uu____10603 with
                                | (uu____10719,xs_sorts,xs) ->
                                    let app =
                                      FStar_SMTEncoding_Util.mkApp
                                        (aname, xs)
                                       in
                                    let a_eq =
                                      FStar_SMTEncoding_Term.Assume
                                        (let _0_896 =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_895 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (let _0_894 =
                                                     mk_Apply tm xs_sorts  in
                                                   (app, _0_894))
                                                 in
                                              ([[app]], xs_sorts, _0_895))
                                            in
                                         (_0_896, (Some "Action equality"),
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
                                        (let _0_898 =
                                           FStar_SMTEncoding_Util.mkForall
                                             (let _0_897 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (tok_app, app)
                                                 in
                                              ([[tok_app]], xs_sorts, _0_897))
                                            in
                                         (_0_898,
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
               let uu____10755 =
                 FStar_Util.fold_map encode_action env
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____10755 with
                | (env,decls2) -> ((FStar_List.flatten decls2), env)))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10771,uu____10772,uu____10773,uu____10774) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____10777 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____10777 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10788,t,quals,uu____10791) ->
          let will_encode_definition =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___126_10796  ->
                       match uu___126_10796 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _
                           |FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____10799 -> false)))
             in
          (match will_encode_definition with
           | true  -> ([], env)
           | uu____10803 ->
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_constant None
                  in
               let uu____10805 = encode_top_level_val env fv t quals  in
               (match uu____10805 with
                | (decls,env) ->
                    let tname = lid.FStar_Ident.str  in
                    let tsym =
                      FStar_SMTEncoding_Util.mkFreeV
                        (tname, FStar_SMTEncoding_Term.Term_sort)
                       in
                    let _0_900 =
                      let _0_899 =
                        primitive_type_axioms env.tcenv lid tname tsym  in
                      FStar_List.append decls _0_899  in
                    (_0_900, env)))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____10820,uu____10821) ->
          let uu____10824 = encode_formula f env  in
          (match uu____10824 with
           | (f,decls) ->
               let g =
                 let _0_904 =
                   FStar_SMTEncoding_Term.Assume
                     (let _0_903 =
                        Some
                          (let _0_901 = FStar_Syntax_Print.lid_to_string l
                              in
                           FStar_Util.format1 "Assumption: %s" _0_901)
                         in
                      let _0_902 =
                        Some
                          (varops.mk_unique
                             (Prims.strcat "assumption_" l.FStar_Ident.str))
                         in
                      (f, _0_903, _0_902))
                    in
                 [_0_904]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____10838,quals,uu____10840)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____10848 =
            FStar_Util.fold_map
              (fun env  ->
                 fun lb  ->
                   let lid =
                     ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let uu____10859 =
                     let _0_905 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone _0_905  in
                   match uu____10859 with
                   | true  ->
                       let val_decl =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp), quals, r)
                          in
                       let uu____10874 = encode_sigelt' env val_decl  in
                       (match uu____10874 with | (decls,env) -> (env, decls))
                   | uu____10881 -> (env, [])) env (Prims.snd lbs)
             in
          (match uu____10848 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10891,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                          FStar_Syntax_Syntax.lbunivs = uu____10893;
                          FStar_Syntax_Syntax.lbtyp = uu____10894;
                          FStar_Syntax_Syntax.lbeff = uu____10895;
                          FStar_Syntax_Syntax.lbdef = uu____10896;_}::[]),uu____10897,uu____10898,uu____10899,uu____10900)
          when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid
          ->
          let uu____10916 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10916 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp
                   (let _0_907 =
                      let _0_906 =
                        FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                      [_0_906]  in
                    ("Valid", _0_907))
                  in
               let decls =
                 let _0_912 =
                   let _0_911 =
                     FStar_SMTEncoding_Term.Assume
                       (let _0_910 =
                          FStar_SMTEncoding_Util.mkForall
                            (let _0_909 =
                               FStar_SMTEncoding_Util.mkEq
                                 (let _0_908 =
                                    FStar_SMTEncoding_Util.mkApp
                                      ("BoxBool_proj_0", [x])
                                     in
                                  (valid_b2t_x, _0_908))
                                in
                             ([[valid_b2t_x]], [xx], _0_909))
                           in
                        (_0_910, (Some "b2t def"), (Some "b2t_def")))
                      in
                   [_0_911]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: _0_912
                  in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____10955,uu____10956,uu____10957,quals,uu____10959) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___127_10967  ->
                  match uu___127_10967 with
                  | FStar_Syntax_Syntax.Discriminator uu____10968 -> true
                  | uu____10969 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____10971,uu____10972,lids,quals,uu____10975) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let _0_913 =
                     (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText  in
                   _0_913 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___128_10985  ->
                     match uu___128_10985 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10986 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____10989,uu____10990,quals,uu____10992) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___129_11004  ->
                  match uu___129_11004 with
                  | FStar_Syntax_Syntax.Projector uu____11005 -> true
                  | uu____11008 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____11015 = try_lookup_free_var env l  in
          (match uu____11015 with
           | Some uu____11019 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l))
                  in
               encode_sigelt env se)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____11028,uu____11029,quals,uu____11031) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let reify_lb lb =
            let uu____11048 =
              (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
               in
            match uu____11048 with
            | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____11051) ->
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
                  let uu____11108 =
                    FStar_Syntax_Util.arrow_formals_comp
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  match uu____11108 with
                  | (formals,comp) ->
                      let reified_typ =
                        FStar_TypeChecker_Util.reify_comp
                          (let uu___155_11125 = env.tcenv  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___155_11125.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___155_11125.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___155_11125.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___155_11125.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___155_11125.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___155_11125.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___155_11125.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___155_11125.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___155_11125.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___155_11125.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___155_11125.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___155_11125.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___155_11125.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___155_11125.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___155_11125.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___155_11125.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___155_11125.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___155_11125.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___155_11125.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.type_of =
                               (uu___155_11125.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___155_11125.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___155_11125.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qname_and_index =
                               (uu___155_11125.FStar_TypeChecker_Env.qname_and_index)
                           }) (FStar_Syntax_Util.lcomp_of_comp comp)
                          FStar_Syntax_Syntax.U_unknown
                         in
                      let _0_914 = FStar_Syntax_Syntax.mk_Total reified_typ
                         in
                      FStar_Syntax_Util.arrow formals _0_914
                   in
                let lb =
                  let uu___156_11127 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___156_11127.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___156_11127.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp = lb_typ;
                    FStar_Syntax_Syntax.lbeff =
                      (uu___156_11127.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = tm'
                  }  in
                ((let uu____11129 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug env.tcenv)
                      (FStar_Options.Other "SMTEncodingReify")
                     in
                  match uu____11129 with
                  | true  ->
                      let _0_917 =
                        FStar_Syntax_Print.lbname_to_string
                          lb.FStar_Syntax_Syntax.lbname
                         in
                      let _0_916 = FStar_Syntax_Print.term_to_string tm  in
                      let _0_915 = FStar_Syntax_Print.term_to_string tm'  in
                      FStar_Util.print3 "%s: Reified %s\nto %s\n" _0_917
                        _0_916 _0_915
                  | uu____11130 -> ());
                 lb)
            | uu____11131 ->
                failwith
                  (let _0_918 =
                     FStar_Syntax_Print.lbname_to_string
                       lb.FStar_Syntax_Syntax.lbname
                      in
                   FStar_Util.format1
                     "Unable to reify %s at smt encoding. It might be time to have a more robust code for this cases."
                     _0_918)
             in
          let _0_920 =
            let _0_919 = FStar_List.map reify_lb bindings  in
            (is_rec, _0_919)  in
          encode_top_level_let env _0_920 quals
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____11135,uu____11136,quals,uu____11138) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____11152,uu____11153,uu____11154) ->
          let uu____11161 = encode_signature env ses  in
          (match uu____11161 with
           | (g,env) ->
               let uu____11171 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___130_11181  ->
                         match uu___130_11181 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____11182,Some "inversion axiom",uu____11183)
                             -> false
                         | uu____11187 -> true))
                  in
               (match uu____11171 with
                | (g',inversions) ->
                    let uu____11196 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___131_11206  ->
                              match uu___131_11206 with
                              | FStar_SMTEncoding_Term.DeclFun uu____11207 ->
                                  true
                              | uu____11213 -> false))
                       in
                    (match uu____11196 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____11224,tps,k,uu____11227,datas,quals,uu____11230) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___132_11239  ->
                    match uu___132_11239 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11240 -> false))
             in
          let constructor_or_logic_type_decl c =
            match is_logical with
            | true  ->
                let uu____11263 = c  in
                (match uu____11263 with
                 | (name,args,uu____11275,uu____11276,uu____11277) ->
                     let _0_922 =
                       FStar_SMTEncoding_Term.DeclFun
                         (let _0_921 =
                            FStar_All.pipe_right args
                              (FStar_List.map Prims.snd)
                             in
                          (name, _0_921, FStar_SMTEncoding_Term.Term_sort,
                            None))
                        in
                     [_0_922])
            | uu____11292 -> FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____11307 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let _0_923 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right _0_923 FStar_Option.isNone))
               in
            match uu____11307 with
            | true  -> []
            | uu____11316 ->
                let uu____11317 =
                  fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
                (match uu____11317 with
                 | (xxsym,xx) ->
                     let uu____11323 =
                       FStar_All.pipe_right datas
                         (FStar_List.fold_left
                            (fun uu____11334  ->
                               fun l  ->
                                 match uu____11334 with
                                 | (out,decls) ->
                                     let uu____11346 =
                                       FStar_TypeChecker_Env.lookup_datacon
                                         env.tcenv l
                                        in
                                     (match uu____11346 with
                                      | (uu____11352,data_t) ->
                                          let uu____11354 =
                                            FStar_Syntax_Util.arrow_formals
                                              data_t
                                             in
                                          (match uu____11354 with
                                           | (args,res) ->
                                               let indices =
                                                 let uu____11383 =
                                                   (FStar_Syntax_Subst.compress
                                                      res).FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____11383 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____11389,indices) ->
                                                     indices
                                                 | uu____11405 -> []  in
                                               let env =
                                                 FStar_All.pipe_right args
                                                   (FStar_List.fold_left
                                                      (fun env  ->
                                                         fun uu____11417  ->
                                                           match uu____11417
                                                           with
                                                           | (x,uu____11421)
                                                               ->
                                                               let _0_925 =
                                                                 FStar_SMTEncoding_Util.mkApp
                                                                   (let _0_924
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x  in
                                                                    (_0_924,
                                                                    [xx]))
                                                                  in
                                                               push_term_var
                                                                 env x _0_925)
                                                      env)
                                                  in
                                               let uu____11423 =
                                                 encode_args indices env  in
                                               (match uu____11423 with
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
                                                      | uu____11441 -> ());
                                                     (let eqs =
                                                        let _0_927 =
                                                          FStar_List.map2
                                                            (fun v  ->
                                                               fun a  ->
                                                                 FStar_SMTEncoding_Util.mkEq
                                                                   (let _0_926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    (_0_926,
                                                                    a))) vars
                                                            indices
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_927
                                                          FStar_SMTEncoding_Util.mk_and_l
                                                         in
                                                      let _0_930 =
                                                        FStar_SMTEncoding_Util.mkOr
                                                          (let _0_929 =
                                                             FStar_SMTEncoding_Util.mkAnd
                                                               (let _0_928 =
                                                                  mk_data_tester
                                                                    env l xx
                                                                   in
                                                                (_0_928, eqs))
                                                              in
                                                           (out, _0_929))
                                                         in
                                                      (_0_930,
                                                        (FStar_List.append
                                                           decls decls'))))))))
                            (FStar_SMTEncoding_Util.mkFalse, []))
                        in
                     (match uu____11323 with
                      | (data_ax,decls) ->
                          let uu____11457 =
                            fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                             in
                          (match uu____11457 with
                           | (ffsym,ff) ->
                               let fuel_guarded_inversion =
                                 let xx_has_type_sfuel =
                                   match (FStar_List.length datas) >
                                           (Prims.parse_int "1")
                                   with
                                   | true  ->
                                       let _0_931 =
                                         FStar_SMTEncoding_Util.mkApp
                                           ("SFuel", [ff])
                                          in
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         _0_931 xx tapp
                                   | uu____11469 ->
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp
                                    in
                                 FStar_SMTEncoding_Term.Assume
                                   (let _0_935 =
                                      FStar_SMTEncoding_Util.mkForall
                                        (let _0_933 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let _0_932 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_sfuel, data_ax)
                                            in
                                         ([[xx_has_type_sfuel]], _0_933,
                                           _0_932))
                                       in
                                    let _0_934 =
                                      Some
                                        (varops.mk_unique
                                           (Prims.strcat
                                              "fuel_guarded_inversion_"
                                              t.FStar_Ident.str))
                                       in
                                    (_0_935, (Some "inversion axiom"),
                                      _0_934))
                                  in
                               let pattern_guarded_inversion =
                                 let uu____11485 =
                                   (contains_name env "Prims.inversion") &&
                                     ((FStar_List.length datas) >
                                        (Prims.parse_int "1"))
                                    in
                                 match uu____11485 with
                                 | true  ->
                                     let xx_has_type_fuel =
                                       FStar_SMTEncoding_Term.mk_HasTypeFuel
                                         ff xx tapp
                                        in
                                     let pattern_guard =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("Prims.inversion", [tapp])
                                        in
                                     let _0_940 =
                                       FStar_SMTEncoding_Term.Assume
                                         (let _0_939 =
                                            FStar_SMTEncoding_Util.mkForall
                                              (let _0_937 =
                                                 add_fuel
                                                   (ffsym,
                                                     FStar_SMTEncoding_Term.Fuel_sort)
                                                   ((xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   :: vars)
                                                  in
                                               let _0_936 =
                                                 FStar_SMTEncoding_Util.mkImp
                                                   (xx_has_type_fuel,
                                                     data_ax)
                                                  in
                                               ([[xx_has_type_fuel;
                                                 pattern_guard]], _0_937,
                                                 _0_936))
                                             in
                                          let _0_938 =
                                            Some
                                              (varops.mk_unique
                                                 (Prims.strcat
                                                    "pattern_guarded_inversion_"
                                                    t.FStar_Ident.str))
                                             in
                                          (_0_939, (Some "inversion axiom"),
                                            _0_938))
                                        in
                                     [_0_940]
                                 | uu____11506 -> []  in
                               FStar_List.append decls
                                 (FStar_List.append [fuel_guarded_inversion]
                                    pattern_guarded_inversion))))
             in
          let uu____11507 =
            let uu____11515 =
              (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n  in
            match uu____11515 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____11542 -> (tps, k)  in
          (match uu____11507 with
           | (formals,res) ->
               let uu____11557 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11557 with
                | (formals,res) ->
                    let uu____11564 = encode_binders None formals env  in
                    (match uu____11564 with
                     | (vars,guards,env',binder_decls,uu____11579) ->
                         let uu____11586 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____11586 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (let _0_941 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, _0_941))
                                 in
                              let uu____11602 =
                                let tname_decl =
                                  constructor_or_logic_type_decl
                                    (let _0_943 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun uu____11619  ->
                                               match uu____11619 with
                                               | (n,s) ->
                                                   ((Prims.strcat tname n),
                                                     s)))
                                        in
                                     let _0_942 = varops.next_id ()  in
                                     (tname, _0_943,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       _0_942, false))
                                   in
                                let uu____11626 =
                                  match vars with
                                  | [] ->
                                      let _0_947 =
                                        let _0_946 =
                                          let _0_945 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_944  -> Some _0_944)
                                            _0_945
                                           in
                                        push_free_var env t tname _0_946  in
                                      ([], _0_947)
                                  | uu____11636 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let _0_948 = varops.next_id ()  in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          _0_948
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        FStar_SMTEncoding_Term.Assume
                                          (let _0_950 =
                                             FStar_SMTEncoding_Util.mkForall'
                                               (let _0_949 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats, None, vars, _0_949))
                                              in
                                           (_0_950,
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
                                match uu____11626 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env)
                                 in
                              (match uu____11602 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____11673 =
                                       encode_term_pred None res env' tapp
                                        in
                                     match uu____11673 with
                                     | (k,decls) ->
                                         let karr =
                                           match (FStar_List.length formals)
                                                   > (Prims.parse_int "0")
                                           with
                                           | true  ->
                                               let _0_953 =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_952 =
                                                      let _0_951 =
                                                        FStar_SMTEncoding_Term.mk_PreType
                                                          ttok_tm
                                                         in
                                                      FStar_SMTEncoding_Term.mk_tester
                                                        "Tm_arrow" _0_951
                                                       in
                                                    (_0_952,
                                                      (Some "kinding"),
                                                      (Some
                                                         (Prims.strcat
                                                            "pre_kinding_"
                                                            ttok))))
                                                  in
                                               [_0_953]
                                           | uu____11689 -> []  in
                                         let _0_958 =
                                           let _0_957 =
                                             let _0_956 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_955 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      (let _0_954 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k)
                                                          in
                                                       ([[tapp]], vars,
                                                         _0_954))
                                                     in
                                                  (_0_955, None,
                                                    (Some
                                                       (Prims.strcat
                                                          "kinding_" ttok))))
                                                in
                                             [_0_956]  in
                                           FStar_List.append karr _0_957  in
                                         FStar_List.append decls _0_958
                                      in
                                   let aux =
                                     let _0_962 =
                                       let _0_961 =
                                         inversion_axioms tapp vars  in
                                       let _0_960 =
                                         let _0_959 = pretype_axiom tapp vars
                                            in
                                         [_0_959]  in
                                       FStar_List.append _0_961 _0_960  in
                                     FStar_List.append kindingAx _0_962  in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11703,uu____11704,uu____11705,uu____11706,uu____11707,uu____11708,uu____11709)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11716,t,uu____11718,n_tps,quals,uu____11721,drange) ->
          let uu____11727 = new_term_constant_and_tok_from_lid env d  in
          (match uu____11727 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____11738 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____11738 with
                | (formals,t_res) ->
                    let uu____11760 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____11760 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11769 =
                           encode_binders (Some fuel_tm) formals env  in
                         (match uu____11769 with
                          | (vars,guards,env',binder_decls,names) ->
                              let projectors =
                                FStar_All.pipe_right names
                                  (FStar_List.map
                                     (fun x  ->
                                        let _0_963 =
                                          mk_term_projector_name d x  in
                                        (_0_963,
                                          FStar_SMTEncoding_Term.Term_sort)))
                                 in
                              let datacons =
                                let _0_965 =
                                  let _0_964 = varops.next_id ()  in
                                  (ddconstrsym, projectors,
                                    FStar_SMTEncoding_Term.Term_sort, _0_964,
                                    true)
                                   in
                                FStar_All.pipe_right _0_965
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
                              let uu____11822 =
                                encode_term_pred None t env ddtok_tm  in
                              (match uu____11822 with
                               | (tok_typing,decls3) ->
                                   let uu____11829 =
                                     encode_binders (Some fuel_tm) formals
                                       env
                                      in
                                   (match uu____11829 with
                                    | (vars',guards',env'',decls_formals,uu____11844)
                                        ->
                                        let uu____11851 =
                                          let xvars =
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
                                        (match uu____11851 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11870 ->
                                                   let _0_967 =
                                                     let _0_966 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       _0_966
                                                      in
                                                   [_0_967]
                                                in
                                             let encode_elim uu____11880 =
                                               let uu____11881 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11881 with
                                               | (head,args) ->
                                                   let uu____11910 =
                                                     (FStar_Syntax_Subst.compress
                                                        head).FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11910 with
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
                                                        let uu____11926 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____11926
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let uu____11937
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____11948
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____11948
                                                                    with
                                                                    | 
                                                                    (env,arg_vars,eqns)
                                                                    ->
                                                                    let uu____11967
                                                                    =
                                                                    let _0_968
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env
                                                                    _0_968
                                                                     in
                                                                    (match uu____11967
                                                                    with
                                                                    | 
                                                                    (uu____11976,xv,env)
                                                                    ->
                                                                    let _0_970
                                                                    =
                                                                    let _0_969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    _0_969 ::
                                                                    eqns  in
                                                                    (env, (xv
                                                                    ::
                                                                    arg_vars),
                                                                    _0_970)))
                                                                 (env', [],
                                                                   [])
                                                                 encoded_args
                                                                in
                                                             (match uu____11937
                                                              with
                                                              | (uu____11986,arg_vars,eqns)
                                                                  ->
                                                                  let arg_vars
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
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_974
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_973
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_972
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_971
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    eqns
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    _0_971))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_973,
                                                                    _0_972))
                                                                     in
                                                                    (_0_974,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))))
                                                                     in
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
                                                                    let _0_975
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (_0_975,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_983
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_981
                                                                    =
                                                                    let _0_977
                                                                    =
                                                                    let _0_976
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    [_0_976]
                                                                     in
                                                                    [_0_977]
                                                                     in
                                                                    let _0_980
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_979
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let _0_978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    (_0_979,
                                                                    _0_978))
                                                                     in
                                                                    (_0_981,
                                                                    [x],
                                                                    _0_980))
                                                                     in
                                                                    let _0_982
                                                                    =
                                                                    Some
                                                                    (varops.mk_unique
                                                                    "lextop")
                                                                     in
                                                                    (_0_983,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    _0_982))
                                                                    | 
                                                                    uu____12036
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
                                                                    let _0_985
                                                                    =
                                                                    let _0_984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    _0_984
                                                                    dapp  in
                                                                    [_0_985]
                                                                    | 
                                                                    uu____12047
                                                                    ->
                                                                    failwith
                                                                    "unexpected sort"))
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_989
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_988
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_986
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    _0_986))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_988,
                                                                    _0_987))
                                                                     in
                                                                    (_0_989,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))))
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____12061 ->
                                                        ((let _0_992 =
                                                            let _0_991 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let _0_990 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              _0_991 _0_990
                                                             in
                                                          FStar_Errors.warn
                                                            drange _0_992);
                                                         ([], [])))
                                                in
                                             let uu____12065 = encode_elim ()
                                                in
                                             (match uu____12065 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let _0_1013 =
                                                      let _0_1012 =
                                                        let _0_1011 =
                                                          let _0_1010 =
                                                            let _0_995 =
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                (let _0_994 =
                                                                   Some
                                                                    (let _0_993
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    _0_993)
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   _0_994))
                                                               in
                                                            [_0_995]  in
                                                          let _0_1009 =
                                                            let _0_1008 =
                                                              let _0_1007 =
                                                                let _0_1006 =
                                                                  let _0_1005
                                                                    =
                                                                    let _0_1004
                                                                    =
                                                                    let _0_1003
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_997
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_996
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_996))
                                                                     in
                                                                    (_0_997,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))))
                                                                     in
                                                                    let _0_1002
                                                                    =
                                                                    let _0_1001
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1000
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_999
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let _0_998
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    _0_999,
                                                                    _0_998))
                                                                     in
                                                                    (_0_1000,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))))
                                                                     in
                                                                    [_0_1001]
                                                                     in
                                                                    _0_1003
                                                                    ::
                                                                    _0_1002
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
                                                                    _0_1004
                                                                     in
                                                                  FStar_List.append
                                                                    _0_1005
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  _0_1006
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                _0_1007
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              _0_1008
                                                             in
                                                          FStar_List.append
                                                            _0_1010 _0_1009
                                                           in
                                                        FStar_List.append
                                                          decls3 _0_1011
                                                         in
                                                      FStar_List.append
                                                        decls2 _0_1012
                                                       in
                                                    FStar_List.append
                                                      binder_decls _0_1013
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
           (fun uu____12110  ->
              fun se  ->
                match uu____12110 with
                | (g,env) ->
                    let uu____12122 = encode_sigelt env se  in
                    (match uu____12122 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____12158 =
        match uu____12158 with
        | (i,decls,env) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____12176 ->
                 ((i + (Prims.parse_int "1")), [], env)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____12181 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   match uu____12181 with
                   | true  ->
                       let _0_1016 = FStar_Syntax_Print.bv_to_string x  in
                       let _0_1015 =
                         FStar_Syntax_Print.term_to_string
                           x.FStar_Syntax_Syntax.sort
                          in
                       let _0_1014 = FStar_Syntax_Print.term_to_string t1  in
                       FStar_Util.print3 "Normalized %s : %s to %s\n" _0_1016
                         _0_1015 _0_1014
                   | uu____12182 -> ());
                  (let uu____12183 = encode_term t1 env  in
                   match uu____12183 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12193 =
                         let _0_1021 =
                           let _0_1020 =
                             let _0_1019 = FStar_Util.digest_of_string t_hash
                                in
                             let _0_1018 =
                               let _0_1017 = FStar_Util.string_of_int i  in
                               Prims.strcat "_" _0_1017  in
                             Prims.strcat _0_1019 _0_1018  in
                           Prims.strcat "x_" _0_1020  in
                         new_term_constant_from_string env x _0_1021  in
                       (match uu____12193 with
                        | (xxsym,xx,env') ->
                            let t =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____12207 = FStar_Options.log_queries ()
                                 in
                              match uu____12207 with
                              | true  ->
                                  Some
                                    (let _0_1024 =
                                       FStar_Syntax_Print.bv_to_string x  in
                                     let _0_1023 =
                                       FStar_Syntax_Print.term_to_string
                                         x.FStar_Syntax_Syntax.sort
                                        in
                                     let _0_1022 =
                                       FStar_Syntax_Print.term_to_string t1
                                        in
                                     FStar_Util.format3 "%s : %s (%s)"
                                       _0_1024 _0_1023 _0_1022)
                              | uu____12209 -> None  in
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____12221,t)) ->
                 let t_norm = whnf env t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____12230 = encode_free_var env fv t t_norm []  in
                 (match uu____12230 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____12249 = encode_sigelt env se  in
                 (match uu____12249 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____12259 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____12259 with | (uu____12271,decls,env) -> (decls, env)
  
let encode_labels labs =
  let prefix =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____12316  ->
            match uu____12316 with
            | (l,uu____12323,uu____12324) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____12345  ->
            match uu____12345 with
            | (l,uu____12353,uu____12354) ->
                let _0_1028 =
                  FStar_All.pipe_left
                    (fun _0_1025  -> FStar_SMTEncoding_Term.Echo _0_1025)
                    (Prims.fst l)
                   in
                let _0_1027 =
                  let _0_1026 =
                    FStar_SMTEncoding_Term.Eval
                      (FStar_SMTEncoding_Util.mkFreeV l)
                     in
                  [_0_1026]  in
                _0_1028 :: _0_1027))
     in
  (prefix, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let _0_1031 =
      let _0_1030 =
        let _0_1029 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = _0_1029;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [_0_1030]  in
    FStar_ST.write last_env _0_1031
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____12380 = FStar_ST.read last_env  in
    match uu____12380 with
    | [] -> failwith "No env; call init first!"
    | e::uu____12386 ->
        let uu___157_12388 = e  in
        {
          bindings = (uu___157_12388.bindings);
          depth = (uu___157_12388.depth);
          tcenv;
          warn = (uu___157_12388.warn);
          cache = (uu___157_12388.cache);
          nolabels = (uu___157_12388.nolabels);
          use_zfuel_name = (uu___157_12388.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___157_12388.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____12392 = FStar_ST.read last_env  in
    match uu____12392 with
    | [] -> failwith "Empty env stack"
    | uu____12397::tl -> FStar_ST.write last_env (env :: tl)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____12405  ->
    let uu____12406 = FStar_ST.read last_env  in
    match uu____12406 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache  in
        let top =
          let uu___158_12427 = hd  in
          {
            bindings = (uu___158_12427.bindings);
            depth = (uu___158_12427.depth);
            tcenv = (uu___158_12427.tcenv);
            warn = (uu___158_12427.warn);
            cache = refs;
            nolabels = (uu___158_12427.nolabels);
            use_zfuel_name = (uu___158_12427.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_12427.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd :: tl)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____12433  ->
    let uu____12434 = FStar_ST.read last_env  in
    match uu____12434 with
    | [] -> failwith "Popping an empty stack"
    | uu____12439::tl -> FStar_ST.write last_env tl
  
let mark_env : Prims.unit -> Prims.unit = fun uu____12447  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____12450  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____12453  ->
    let uu____12454 = FStar_ST.read last_env  in
    match uu____12454 with
    | hd::uu____12460::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____12466 -> failwith "Impossible"
  
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
        let uu____12511 = FStar_Options.log_queries ()  in
        match uu____12511 with
        | true  ->
            let _0_1034 =
              FStar_SMTEncoding_Term.Caption
                (let _0_1033 =
                   let _0_1032 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Syntax_Print.lid_to_string)
                      in
                   FStar_All.pipe_right _0_1032 (FStar_String.concat ", ")
                    in
                 Prims.strcat "encoding sigelt " _0_1033)
               in
            _0_1034 :: decls
        | uu____12516 -> decls  in
      let env = get_env tcenv  in
      let uu____12518 = encode_sigelt env se  in
      match uu____12518 with
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
           | uu____12531 -> "module")
          (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____12533 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       match uu____12533 with
       | true  ->
           let _0_1035 =
             FStar_All.pipe_right
               (FStar_List.length modul.FStar_Syntax_Syntax.exports)
               FStar_Util.string_of_int
              in
           FStar_Util.print2
             "+++++++++++Encoding externals for %s ... %s exports\n" name
             _0_1035
       | uu____12536 -> ());
      (let env = get_env tcenv  in
       let uu____12538 =
         encode_signature
           (let uu___159_12542 = env  in
            {
              bindings = (uu___159_12542.bindings);
              depth = (uu___159_12542.depth);
              tcenv = (uu___159_12542.tcenv);
              warn = false;
              cache = (uu___159_12542.cache);
              nolabels = (uu___159_12542.nolabels);
              use_zfuel_name = (uu___159_12542.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___159_12542.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____12538 with
       | (decls,env) ->
           let caption decls =
             let uu____12554 = FStar_Options.log_queries ()  in
             match uu____12554 with
             | true  ->
                 let msg = Prims.strcat "Externals for " name  in
                 FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                   decls)
                   [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             | uu____12557 -> decls  in
           (set_env
              (let uu___160_12559 = env  in
               {
                 bindings = (uu___160_12559.bindings);
                 depth = (uu___160_12559.depth);
                 tcenv = (uu___160_12559.tcenv);
                 warn = true;
                 cache = (uu___160_12559.cache);
                 nolabels = (uu___160_12559.nolabels);
                 use_zfuel_name = (uu___160_12559.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___160_12559.encode_non_total_function_typ)
               });
            (let uu____12561 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             match uu____12561 with
             | true  ->
                 FStar_Util.print1 "Done encoding externals for %s\n" name
             | uu____12562 -> ());
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
         let uu____12603 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____12624 = aux rest  in
                 (match uu____12624 with
                  | (out,rest) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort
                         in
                      let _0_1037 =
                        let _0_1036 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___161_12642 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___161_12642.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___161_12642.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             })
                           in
                        _0_1036 :: out  in
                      (_0_1037, rest))
             | uu____12643 -> ([], bindings)  in
           let uu____12647 = aux bindings  in
           match uu____12647 with
           | (closing,bindings) ->
               let _0_1038 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q
                  in
               (_0_1038, bindings)
            in
         match uu____12603 with
         | (q,bindings) ->
             let uu____12673 =
               let _0_1039 =
                 FStar_List.filter
                   (fun uu___133_12676  ->
                      match uu___133_12676 with
                      | FStar_TypeChecker_Env.Binding_sig uu____12677 ->
                          false
                      | uu____12681 -> true) bindings
                  in
               encode_env_bindings env _0_1039  in
             (match uu____12673 with
              | (env_decls,env) ->
                  ((let uu____12692 =
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
                    match uu____12692 with
                    | true  ->
                        let _0_1040 = FStar_Syntax_Print.term_to_string q  in
                        FStar_Util.print1 "Encoding query formula: %s\n"
                          _0_1040
                    | uu____12693 -> ());
                   (let uu____12694 = encode_formula q env  in
                    match uu____12694 with
                    | (phi,qdecls) ->
                        let uu____12706 =
                          let _0_1041 = FStar_TypeChecker_Env.get_range tcenv
                             in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg _0_1041 phi
                           in
                        (match uu____12706 with
                         | (labels,phi) ->
                             let uu____12718 = encode_labels labels  in
                             (match uu____12718 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_1043 =
                                         FStar_SMTEncoding_Util.mkNot phi  in
                                       let _0_1042 =
                                         Some (varops.mk_unique "@query")  in
                                       (_0_1043, (Some "query"), _0_1042))
                                     in
                                  let suffix =
                                    let _0_1045 =
                                      let _0_1044 =
                                        let uu____12743 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        match uu____12743 with
                                        | true  ->
                                            [FStar_SMTEncoding_Term.PrintStats]
                                        | uu____12745 -> []  in
                                      FStar_List.append _0_1044
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix _0_1045
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____12756 = encode_formula q env  in
       match uu____12756 with
       | (f,uu____12760) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____12762) -> true
             | uu____12765 -> false)))
  