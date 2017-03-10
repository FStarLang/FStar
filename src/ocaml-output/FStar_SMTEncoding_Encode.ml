open Prims
let add_fuel x tl =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
  if uu____16 then tl else x :: tl 
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c) 
let vargs args =
  FStar_List.filter
    (fun uu___108_74  ->
       match uu___108_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
  
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l) ->
      Some
        (FStar_Util.Inl
           (let _0_277 =
              let _0_276 = l.FStar_Syntax_Syntax.comp ()  in
              FStar_Syntax_Subst.subst_comp s _0_276  in
            FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_277))
  | uu____118 -> l 
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a =
        let uu___132_132 = a  in
        let _0_278 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = _0_278;
          FStar_Syntax_Syntax.index =
            (uu___132_132.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___132_132.FStar_Syntax_Syntax.sort)
        }  in
      let _0_279 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape _0_279
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____145 =
          failwith
            (FStar_Util.format2
               "Projector %s on data constructor %s not found"
               (Prims.string_of_int i) lid.FStar_Ident.str)
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
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____179 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let _0_280 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape _0_280
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_281 = mk_term_projector_name lid a  in
         (_0_281,
           (FStar_SMTEncoding_Term.Arrow
              (FStar_SMTEncoding_Term.Term_sort,
                FStar_SMTEncoding_Term.Term_sort))))
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_282 = mk_term_projector_name_by_pos lid i  in
         (_0_282,
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
    let _0_284 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let _0_283 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (_0_284, _0_283)  in
  let scopes = FStar_Util.mk_ref (let _0_285 = new_scope ()  in [_0_285])  in
  let mk_unique y =
    let y = escape y  in
    let y =
      let uu____417 =
        let _0_286 = FStar_ST.read scopes  in
        FStar_Util.find_map _0_286
          (fun uu____430  ->
             match uu____430 with
             | (names,uu____437) -> FStar_Util.smap_try_find names y)
         in
      match uu____417 with
      | None  -> y
      | Some uu____442 ->
          (FStar_Util.incr ctr;
           (let _0_288 =
              let _0_287 = Prims.string_of_int (FStar_ST.read ctr)  in
              Prims.strcat "__" _0_287  in
            Prims.strcat y _0_288))
       in
    let top_scope =
      let _0_289 = FStar_List.hd (FStar_ST.read scopes)  in
      FStar_All.pipe_left Prims.fst _0_289  in
    FStar_Util.smap_add top_scope y true; y  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id uu____484 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh pfx =
    let _0_291 =
      let _0_290 = next_id ()  in
      FStar_All.pipe_left Prims.string_of_int _0_290  in
    FStar_Util.format2 "%s_%s" pfx _0_291  in
  let string_const s =
    let uu____499 =
      let _0_292 = FStar_ST.read scopes  in
      FStar_Util.find_map _0_292
        (fun uu____512  ->
           match uu____512 with
           | (uu____518,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____499 with
    | Some f -> f
    | None  ->
        let id = next_id ()  in
        let f =
          let _0_293 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _0_293  in
        let top_scope =
          let _0_294 = FStar_List.hd (FStar_ST.read scopes)  in
          FStar_All.pipe_left Prims.snd _0_294  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push uu____551 =
    let _0_297 =
      let _0_296 = new_scope ()  in
      let _0_295 = FStar_ST.read scopes  in _0_296 :: _0_295  in
    FStar_ST.write scopes _0_297  in
  let pop uu____573 =
    let _0_298 = FStar_List.tl (FStar_ST.read scopes)  in
    FStar_ST.write scopes _0_298  in
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
    let uu___133_673 = x  in
    let _0_299 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = _0_299;
      FStar_Syntax_Syntax.index = (uu___133_673.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___133_673.FStar_Syntax_Syntax.sort)
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
    let _0_300 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___109_840  ->
              match uu___109_840 with
              | Binding_var (x,uu____842) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____844,uu____845,uu____846) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right _0_300 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____878 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      if uu____878 then Some (FStar_Syntax_Print.term_to_string t) else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let _0_301 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, _0_301)
  
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
        (let uu___134_901 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___134_901.tcenv);
           warn = (uu___134_901.warn);
           cache = (uu___134_901.cache);
           nolabels = (uu___134_901.nolabels);
           use_zfuel_name = (uu___134_901.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___134_901.encode_non_total_function_typ)
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
        (let uu___135_914 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___135_914.depth);
           tcenv = (uu___135_914.tcenv);
           warn = (uu___135_914.warn);
           cache = (uu___135_914.cache);
           nolabels = (uu___135_914.nolabels);
           use_zfuel_name = (uu___135_914.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___135_914.encode_non_total_function_typ)
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
          (let uu___136_930 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___136_930.depth);
             tcenv = (uu___136_930.tcenv);
             warn = (uu___136_930.warn);
             cache = (uu___136_930.cache);
             nolabels = (uu___136_930.nolabels);
             use_zfuel_name = (uu___136_930.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___136_930.encode_non_total_function_typ)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___137_940 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___137_940.depth);
          tcenv = (uu___137_940.tcenv);
          warn = (uu___137_940.warn);
          cache = (uu___137_940.cache);
          nolabels = (uu___137_940.nolabels);
          use_zfuel_name = (uu___137_940.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___137_940.encode_non_total_function_typ)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___110_956  ->
             match uu___110_956 with
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
                 (let _0_303 = FStar_Syntax_Print.bv_to_string a2  in
                  let _0_302 = print_env env  in
                  FStar_Util.format2
                    "Bound term variable not found (after unmangling): %s in environment: %s"
                    _0_303 _0_302)
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let _0_309 =
        let uu___138_999 = env  in
        let _0_308 =
          let _0_307 =
            Binding_fvar
              (let _0_306 =
                 let _0_305 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                 FStar_All.pipe_left (fun _0_304  -> Some _0_304) _0_305  in
               (x, fname, _0_306, None))
             in
          _0_307 :: (env.bindings)  in
        {
          bindings = _0_308;
          depth = (uu___138_999.depth);
          tcenv = (uu___138_999.tcenv);
          warn = (uu___138_999.warn);
          cache = (uu___138_999.cache);
          nolabels = (uu___138_999.nolabels);
          use_zfuel_name = (uu___138_999.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___138_999.encode_non_total_function_typ)
        }  in
      (fname, ftok, _0_309)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___111_1021  ->
           match uu___111_1021 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1043 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let _0_310 =
        lookup_binding env
          (fun uu___112_1056  ->
             match uu___112_1056 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1066 -> None)
         in
      FStar_All.pipe_right _0_310 FStar_Option.isSome
  
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
            (let _0_311 = FStar_Syntax_Print.lid_to_string a  in
             FStar_Util.format1 "Name not found: %s" _0_311)
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
          let uu___139_1125 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___139_1125.depth);
            tcenv = (uu___139_1125.tcenv);
            warn = (uu___139_1125.warn);
            cache = (uu___139_1125.cache);
            nolabels = (uu___139_1125.nolabels);
            use_zfuel_name = (uu___139_1125.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___139_1125.encode_non_total_function_typ)
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
                (let _0_313 =
                   let _0_312 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                      in
                   [_0_312]  in
                 (f, _0_313))
               in
            let uu___140_1153 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___140_1153.depth);
              tcenv = (uu___140_1153.tcenv);
              warn = (uu___140_1153.warn);
              cache = (uu___140_1153.cache);
              nolabels = (uu___140_1153.nolabels);
              use_zfuel_name = (uu___140_1153.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___140_1153.encode_non_total_function_typ)
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
                           let _0_315 =
                             let _0_314 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right _0_314 Prims.fst  in
                           FStar_Util.starts_with _0_315 "fuel"  in
                         if uu____1198
                         then
                           let _0_318 =
                             let _0_317 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF _0_317 fuel
                              in
                           FStar_All.pipe_left (fun _0_316  -> Some _0_316)
                             _0_318
                         else Some t
                     | uu____1202 -> Some t)
                | uu____1203 -> None))
  
let lookup_free_var env a =
  let uu____1221 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1221 with
  | Some t -> t
  | None  ->
      failwith
        (let _0_319 =
           FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
         FStar_Util.format1 "Name not found: %s" _0_319)
  
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
        (fun uu___113_1325  ->
           match uu___113_1325 with
           | Binding_fvar (uu____1327,nm',tok,uu____1330) when nm = nm' ->
               tok
           | uu____1335 -> None)
  
let mkForall_fuel' n uu____1352 =
  match uu____1352 with
  | (pats,vars,body) ->
      let fallback uu____1368 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1371 = FStar_Options.unthrottle_inductives ()  in
      if uu____1371
      then fallback ()
      else
        (let uu____1373 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
         match uu____1373 with
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
                         let _0_320 = add_fuel [guard]  in
                         FStar_All.pipe_right _0_320 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard, body')
               | uu____1408 -> body  in
             let vars = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars  in
             FStar_SMTEncoding_Util.mkForall (pats, vars, body))
  
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
          let _0_321 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_321 FStar_Option.isNone
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
               (fun uu___114_1499  ->
                  match uu___114_1499 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1500 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1501,uu____1502,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let _0_322 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_322 FStar_Option.isSome
      | uu____1538 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1545 = head_normal env t  in
      if uu____1545
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
    let _0_325 = let _0_323 = FStar_Syntax_Syntax.null_binder t  in [_0_323]
       in
    let _0_324 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs _0_325 _0_324 None
  
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
                    let _0_326 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out _0_326
                | s ->
                    let _0_327 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out _0_327) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___115_1595  ->
    match uu___115_1595 with
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
              if uu____1644 then tok_of_name env f else None
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
              if uu____1660 then Some t else None
          | uu____1664 -> None  in
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
      (let uu____1679 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____1679
       then
         let _0_329 = FStar_Syntax_Print.term_to_string tm  in
         let _0_328 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" _0_329 _0_328
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
    | uu____1761 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___116_1764  ->
    match uu___116_1764 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        FStar_SMTEncoding_Util.mkApp
          (let _0_331 =
             let _0_330 =
               FStar_SMTEncoding_Term.boxInt
                 (FStar_SMTEncoding_Util.mkInteger'
                    (FStar_Util.int_of_char c))
                in
             [_0_330]  in
           ("FStar.Char.Char", _0_331))
    | FStar_Const.Const_int (i,None ) ->
        FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger i)
    | FStar_Const.Const_int (i,Some uu____1774) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1783) ->
        varops.string_const
          (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        failwith
          (let _0_332 = FStar_Syntax_Print.const_to_string c  in
           FStar_Util.format1 "Unhandled constant: %s" _0_332)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1807 -> t
        | FStar_Syntax_Syntax.Tm_refine uu____1815 ->
            let _0_333 = FStar_Syntax_Util.unrefine t  in aux true _0_333
        | uu____1820 ->
            if norm
            then let _0_334 = whnf env t  in aux false _0_334
            else
              failwith
                (let _0_336 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let _0_335 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   _0_336 _0_335)
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
    | uu____1842 ->
        let _0_337 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_337)
  
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
        (let uu____1985 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____1985
         then
           let _0_338 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" _0_338
         else ());
        (let uu____1987 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2023  ->
                   fun b  ->
                     match uu____2023 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2066 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2075 = gen_term_var env x  in
                           match uu____2075 with
                           | (xxsym,xx,env') ->
                               let uu____2089 =
                                 let _0_339 =
                                   norm env x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt _0_339 env xx  in
                               (match uu____2089 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2066 with
                          | (v,g,env,decls',n) ->
                              ((v :: vars), (g :: guards), env,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], []))
            in
         match uu____1987 with
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
          let uu____2179 = encode_term t env  in
          match uu____2179 with
          | (t,decls) ->
              let _0_340 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t  in
              (_0_340, decls)

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
          let uu____2193 = encode_term t env  in
          match uu____2193 with
          | (t,decls) ->
              (match fuel_opt with
               | None  ->
                   let _0_341 = FStar_SMTEncoding_Term.mk_HasTypeZ e t  in
                   (_0_341, decls)
               | Some f ->
                   let _0_342 = FStar_SMTEncoding_Term.mk_HasTypeFuel f e t
                      in
                   (_0_342, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2209 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2209
       then
         let _0_345 = FStar_Syntax_Print.tag_of_term t  in
         let _0_344 = FStar_Syntax_Print.tag_of_term t0  in
         let _0_343 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" _0_345 _0_344 _0_343
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           failwith
             (let _0_349 =
                FStar_All.pipe_left FStar_Range.string_of_range
                  t.FStar_Syntax_Syntax.pos
                 in
              let _0_348 = FStar_Syntax_Print.tag_of_term t0  in
              let _0_347 = FStar_Syntax_Print.term_to_string t0  in
              let _0_346 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_349
                _0_348 _0_347 _0_346)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           failwith
             (let _0_350 = FStar_Syntax_Print.bv_to_string x  in
              FStar_Util.format1 "Impossible: locally nameless; got %s"
                _0_350)
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2221) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2241) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x  in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let _0_351 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name  in
           (_0_351, [])
       | FStar_Syntax_Syntax.Tm_type uu____2255 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t,uu____2258) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let _0_352 = encode_const c  in (_0_352, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2277 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2277 with
            | (binders,res) ->
                let uu____2284 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2284
                then
                  let uu____2287 = encode_binders None binders env  in
                  (match uu____2287 with
                   | (vars,guards,env',decls,uu____2302) ->
                       let fsym =
                         let _0_353 = varops.fresh "f"  in
                         (_0_353, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2314 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_2318 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_2318.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_2318.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_2318.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_2318.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_2318.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_2318.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_2318.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_2318.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_2318.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_2318.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_2318.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_2318.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_2318.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_2318.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_2318.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_2318.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_2318.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_2318.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_2318.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_2318.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_2318.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_2318.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_2318.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____2314 with
                        | (pre_opt,res_t) ->
                            let uu____2325 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2325 with
                             | (res_pred,decls') ->
                                 let uu____2332 =
                                   match pre_opt with
                                   | None  ->
                                       let _0_354 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (_0_354, [])
                                   | Some pre ->
                                       let uu____2341 =
                                         encode_formula pre env'  in
                                       (match uu____2341 with
                                        | (guard,decls0) ->
                                            let _0_355 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (_0_355, decls0))
                                    in
                                 (match uu____2332 with
                                  | (guards,guard_decls) ->
                                      let t_interp =
                                        FStar_SMTEncoding_Util.mkForall
                                          (let _0_356 =
                                             FStar_SMTEncoding_Util.mkImp
                                               (guards, res_pred)
                                              in
                                           ([[app]], vars, _0_356))
                                         in
                                      let cvars =
                                        let _0_357 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right _0_357
                                          (FStar_List.filter
                                             (fun uu____2370  ->
                                                match uu____2370 with
                                                | (x,uu____2374) ->
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
                                      let uu____2385 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2385 with
                                       | Some (t',sorts,uu____2401) ->
                                           let _0_359 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (let _0_358 =
                                                  FStar_All.pipe_right cvars
                                                    (FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV)
                                                   in
                                                (t', _0_358))
                                              in
                                           (_0_359, [])
                                       | None  ->
                                           let tsym =
                                             varops.mk_unique
                                               (let _0_360 =
                                                  FStar_Util.digest_of_string
                                                    tkey_hash
                                                   in
                                                Prims.strcat "Tm_arrow_"
                                                  _0_360)
                                              in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2431 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2431
                                             then
                                               Some
                                                 (FStar_TypeChecker_Normalize.term_to_string
                                                    env.tcenv t0)
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t =
                                             FStar_SMTEncoding_Util.mkApp
                                               (let _0_361 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    cvars
                                                   in
                                                (tsym, _0_361))
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
                                               (let _0_362 =
                                                  FStar_SMTEncoding_Util.mkForall
                                                    ([[t_has_kind]], cvars,
                                                      t_has_kind)
                                                   in
                                                (_0_362, a_name, a_name))
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
                                                 (Prims.strcat "pre_typing_"
                                                    tsym)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               (let _0_366 =
                                                  mkForall_fuel
                                                    (let _0_365 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (let _0_364 =
                                                            let _0_363 =
                                                              FStar_SMTEncoding_Term.mk_PreType
                                                                f
                                                               in
                                                            FStar_SMTEncoding_Term.mk_tester
                                                              "Tm_arrow"
                                                              _0_363
                                                             in
                                                          (f_has_t, _0_364))
                                                        in
                                                     ([[f_has_t]], (fsym ::
                                                       cvars), _0_365))
                                                   in
                                                (_0_366,
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
                                               (let _0_368 =
                                                  FStar_SMTEncoding_Util.mkForall
                                                    (let _0_367 =
                                                       FStar_SMTEncoding_Util.mkIff
                                                         (f_has_t_z,
                                                           t_interp)
                                                        in
                                                     ([[f_has_t_z]], (fsym ::
                                                       cvars), _0_367))
                                                   in
                                                (_0_368, a_name, a_name))
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
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None)
                      in
                   let t = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Some (Prims.strcat "non_total_function_typing_" tsym)
                        in
                     FStar_SMTEncoding_Term.Assume
                       (let _0_369 =
                          FStar_SMTEncoding_Term.mk_HasType t
                            FStar_SMTEncoding_Term.mk_Term_type
                           in
                        (_0_369, (Some "Typing for non-total arrows"),
                          a_name))
                      in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t  in
                   let t_interp =
                     let a_name = Some (Prims.strcat "pre_typing_" tsym)  in
                     FStar_SMTEncoding_Term.Assume
                       (let _0_373 =
                          mkForall_fuel
                            (let _0_372 =
                               FStar_SMTEncoding_Util.mkImp
                                 (let _0_371 =
                                    let _0_370 =
                                      FStar_SMTEncoding_Term.mk_PreType f  in
                                    FStar_SMTEncoding_Term.mk_tester
                                      "Tm_arrow" _0_370
                                     in
                                  (f_has_t, _0_371))
                                in
                             ([[f_has_t]], [fsym], _0_372))
                           in
                        (_0_373, a_name, a_name))
                      in
                   (t, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2529 ->
           let uu____2534 =
             let uu____2537 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2537 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2542;
                 FStar_Syntax_Syntax.pos = uu____2543;
                 FStar_Syntax_Syntax.vars = uu____2544;_} ->
                 let uu____2551 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2551 with
                  | (b,f) ->
                      let _0_374 = Prims.fst (FStar_List.hd b)  in
                      (_0_374, f))
             | uu____2567 -> failwith "impossible"  in
           (match uu____2534 with
            | (x,f) ->
                let uu____2574 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2574 with
                 | (base_t,decls) ->
                     let uu____2581 = gen_term_var env x  in
                     (match uu____2581 with
                      | (x,xtm,env') ->
                          let uu____2590 = encode_formula f env'  in
                          (match uu____2590 with
                           | (refinement,decls') ->
                               let uu____2597 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2597 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (let _0_375 =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm base_t
                                            in
                                         (_0_375, refinement))
                                       in
                                    let cvars =
                                      let _0_376 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right _0_376
                                        (FStar_List.filter
                                           (fun uu____2614  ->
                                              match uu____2614 with
                                              | (y,uu____2618) ->
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
                                    let uu____2637 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2637 with
                                     | Some (t,uu____2652,uu____2653) ->
                                         let _0_378 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_377 =
                                                FStar_All.pipe_right cvars
                                                  (FStar_List.map
                                                     FStar_SMTEncoding_Util.mkFreeV)
                                                 in
                                              (t, _0_377))
                                            in
                                         (_0_378, [])
                                     | None  ->
                                         let tsym =
                                           varops.mk_unique
                                             (let _0_379 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "Tm_refine_"
                                                _0_379)
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
                                             (let _0_380 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (tsym, _0_380))
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
                                             (let _0_382 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_381 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (t_haseq_ref,
                                                         t_haseq_base)
                                                      in
                                                   ([[t_haseq_ref]], cvars,
                                                     _0_381))
                                                 in
                                              (_0_382,
                                                (Some
                                                   (Prims.strcat "haseq for "
                                                      tsym)),
                                                (Some
                                                   (Prims.strcat "haseq" tsym))))
                                            in
                                         let t_kinding =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_383 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  ([[t_has_kind]], cvars,
                                                    t_has_kind)
                                                 in
                                              (_0_383,
                                                (Some "refinement kinding"),
                                                (Some
                                                   (Prims.strcat
                                                      "refinement_kinding_"
                                                      tsym))))
                                            in
                                         let t_interp =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_386 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_384 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (x_has_t, encoding)
                                                      in
                                                   ([[x_has_t]], (ffv :: xfv
                                                     :: cvars), _0_384))
                                                 in
                                              let _0_385 =
                                                Some
                                                  (FStar_Syntax_Print.term_to_string
                                                     t0)
                                                 in
                                              (_0_386, _0_385,
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
           let uu____2755 = encode_term_pred None k env ttm  in
           (match uu____2755 with
            | (t_has_k,decls) ->
                let d =
                  FStar_SMTEncoding_Term.Assume
                    (let _0_389 =
                       Some
                         (varops.mk_unique
                            (let _0_388 =
                               let _0_387 = FStar_Unionfind.uvar_id uv  in
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 _0_387
                                in
                             FStar_Util.format1 "uvar_typing_%s" _0_388))
                        in
                     (t_has_k, (Some "Uvar typing"), _0_389))
                   in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____2769 ->
           let uu____2779 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____2779 with
            | (head,args_e) ->
                let uu____2807 =
                  let _0_390 =
                    (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                     in
                  (_0_390, args_e)  in
                (match uu____2807 with
                 | (uu____2822,uu____2823) when head_redex env head ->
                     let _0_391 = whnf env t  in encode_term _0_391 env
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
                     let uu____2907 = encode_term v1 env  in
                     (match uu____2907 with
                      | (v1,decls1) ->
                          let uu____2914 = encode_term v2 env  in
                          (match uu____2914 with
                           | (v2,decls2) ->
                               let _0_392 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2  in
                               (_0_392, (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____2922) ->
                     let e0 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_394 =
                                let _0_393 = FStar_List.hd args_e  in
                                [_0_393]  in
                              (head, _0_394)))) None
                         head.FStar_Syntax_Syntax.pos
                        in
                     ((let uu____2964 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____2964
                       then
                         let _0_395 = FStar_Syntax_Print.term_to_string e0
                            in
                         FStar_Util.print1 "Trying to normalize %s\n" _0_395
                       else ());
                      (let e0 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0
                          in
                       (let uu____2968 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify")
                           in
                        if uu____2968
                        then
                          let _0_396 = FStar_Syntax_Print.term_to_string e0
                             in
                          FStar_Util.print1 "Result of normalization %s\n"
                            _0_396
                        else ());
                       (let e0 =
                          let uu____2971 =
                            let uu____2972 =
                              (FStar_Syntax_Subst.compress e0).FStar_Syntax_Syntax.n
                               in
                            match uu____2972 with
                            | FStar_Syntax_Syntax.Tm_app uu____2973 -> false
                            | uu____2983 -> true  in
                          if uu____2971
                          then e0
                          else
                            (let uu____2985 =
                               FStar_Syntax_Util.head_and_args e0  in
                             match uu____2985 with
                             | (head,args) ->
                                 let uu____3011 =
                                   let uu____3012 =
                                     (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                                      in
                                   match uu____3012 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3013 -> false  in
                                 if uu____3011
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3029 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e0)
                           in
                        let e =
                          match args_e with
                          | uu____3037::[] -> e0
                          | uu____3050 ->
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    (let _0_397 = FStar_List.tl args_e  in
                                     (e0, _0_397)))) None
                                t0.FStar_Syntax_Syntax.pos
                           in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3073),(arg,uu____3075)::[]) -> encode_term arg env
                 | uu____3093 ->
                     let uu____3101 = encode_args args_e env  in
                     (match uu____3101 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3134 = encode_term head env  in
                            match uu____3134 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3173 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3173 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3215  ->
                                                 fun uu____3216  ->
                                                   match (uu____3215,
                                                           uu____3216)
                                                   with
                                                   | ((bv,uu____3230),
                                                      (a,uu____3232)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e
                                             in
                                          let ty =
                                            let _0_398 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right _0_398
                                              (FStar_Syntax_Subst.subst subst)
                                             in
                                          let uu____3248 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3248 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_401 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        ([[has_type]], cvars,
                                                          has_type)
                                                       in
                                                    let _0_400 =
                                                      Some
                                                        (varops.mk_unique
                                                           (let _0_399 =
                                                              FStar_Util.digest_of_string
                                                                (FStar_SMTEncoding_Term.hash_of_term
                                                                   app_tm)
                                                               in
                                                            Prims.strcat
                                                              "partial_app_typing_"
                                                              _0_399))
                                                       in
                                                    (_0_401,
                                                      (Some
                                                         "Partial app typing"),
                                                      _0_400))
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3279 = lookup_free_var_sym env fv  in
                            match uu____3279 with
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
                                  (let _0_402 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right _0_402 Prims.snd)
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3323,FStar_Util.Inl t,uu____3325) ->
                                Some t
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3346,FStar_Util.Inr c,uu____3348) ->
                                Some (FStar_Syntax_Util.comp_result c)
                            | uu____3369 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type ->
                               let head_type =
                                 let _0_403 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine _0_403
                                  in
                               let uu____3389 =
                                 curried_arrow_formals_comp head_type  in
                               (match uu____3389 with
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
                                     | uu____3414 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3459 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3459 with
            | (bs,body,opening) ->
                let fallback uu____3474 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let _0_404 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (_0_404, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
                  | FStar_Util.Inr (eff,uu____3490) ->
                      let _0_405 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right _0_405 Prims.op_Negation
                   in
                let reify_comp_and_body env c body =
                  let reified_body = reify_body env.tcenv body  in
                  let c =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let _0_406 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___142_3540 = env.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___142_3540.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___142_3540.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___142_3540.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___142_3540.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___142_3540.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___142_3540.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___142_3540.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___142_3540.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___142_3540.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___142_3540.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___142_3540.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___142_3540.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___142_3540.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___142_3540.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___142_3540.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___142_3540.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___142_3540.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___142_3540.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___142_3540.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___142_3540.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___142_3540.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___142_3540.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___142_3540.FStar_TypeChecker_Env.qname_and_index)
                             }) _0_406 FStar_Syntax_Syntax.U_unknown
                           in
                        FStar_Util.Inl
                          (FStar_Syntax_Util.lcomp_of_comp
                             (FStar_Syntax_Syntax.mk_Total typ))
                    | FStar_Util.Inr (eff_name,uu____3545) -> c  in
                  (c, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let _0_409 =
                        let _0_407 = lc.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening _0_407  in
                      FStar_All.pipe_right _0_409
                        (fun _0_408  -> Some _0_408)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar uu____3587 =
                        let _0_410 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right _0_410 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let _0_412 =
                          FStar_Syntax_Syntax.mk_Total (new_uvar ())  in
                        FStar_All.pipe_right _0_412
                          (fun _0_411  -> Some _0_411)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let _0_414 =
                             FStar_Syntax_Syntax.mk_GTotal (new_uvar ())  in
                           FStar_All.pipe_right _0_414
                             (fun _0_413  -> Some _0_413))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let _0_416 =
                         let _0_415 = FStar_Syntax_Print.term_to_string t0
                            in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           _0_415
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_416);
                      fallback ())
                 | Some lc ->
                     let lc = lc  in
                     let uu____3620 =
                       (is_impure lc) &&
                         (Prims.op_Negation
                            (FStar_TypeChecker_Env.is_reifiable env.tcenv lc))
                        in
                     if uu____3620
                     then fallback ()
                     else
                       (let uu____3624 = encode_binders None bs env  in
                        match uu____3624 with
                        | (vars,guards,envbody,decls,uu____3639) ->
                            let uu____3646 =
                              let uu____3654 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc
                                 in
                              if uu____3654
                              then reify_comp_and_body envbody lc body
                              else (lc, body)  in
                            (match uu____3646 with
                             | (lc,body) ->
                                 let uu____3679 = encode_term body envbody
                                    in
                                 (match uu____3679 with
                                  | (body,decls') ->
                                      let key_body =
                                        FStar_SMTEncoding_Util.mkForall
                                          (let _0_418 =
                                             FStar_SMTEncoding_Util.mkImp
                                               (let _0_417 =
                                                  FStar_SMTEncoding_Util.mk_and_l
                                                    guards
                                                   in
                                                (_0_417, body))
                                              in
                                           ([], vars, _0_418))
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
                                      let uu____3697 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____3697 with
                                       | Some (t,uu____3712,uu____3713) ->
                                           let _0_420 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (let _0_419 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    cvars
                                                   in
                                                (t, _0_419))
                                              in
                                           (_0_420, [])
                                       | None  ->
                                           let uu____3732 =
                                             is_eta env vars body  in
                                           (match uu____3732 with
                                            | Some t -> (t, [])
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map Prims.snd
                                                    cvars
                                                   in
                                                let fsym =
                                                  varops.mk_unique
                                                    (let _0_421 =
                                                       FStar_Util.digest_of_string
                                                         tkey_hash
                                                        in
                                                     Prims.strcat "Tm_abs_"
                                                       _0_421)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (let _0_422 =
                                                       FStar_List.map
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                         cvars
                                                        in
                                                     (fsym, _0_422))
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  let uu____3753 =
                                                    codomain_eff lc  in
                                                  match uu____3753 with
                                                  | None  -> []
                                                  | Some c ->
                                                      let tfun =
                                                        FStar_Syntax_Util.arrow
                                                          bs c
                                                         in
                                                      let uu____3760 =
                                                        encode_term_pred None
                                                          tfun env f
                                                         in
                                                      (match uu____3760 with
                                                       | (f_has_t,decls'') ->
                                                           let a_name =
                                                             Some
                                                               (Prims.strcat
                                                                  "typing_"
                                                                  fsym)
                                                              in
                                                           let _0_425 =
                                                             let _0_424 =
                                                               FStar_SMTEncoding_Term.Assume
                                                                 (let _0_423
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    ([[f]],
                                                                    cvars,
                                                                    f_has_t)
                                                                     in
                                                                  (_0_423,
                                                                    a_name,
                                                                    a_name))
                                                                in
                                                             [_0_424]  in
                                                           FStar_List.append
                                                             decls'' _0_425)
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Some
                                                      (Prims.strcat
                                                         "interpretation_"
                                                         fsym)
                                                     in
                                                  FStar_SMTEncoding_Term.Assume
                                                    (let _0_427 =
                                                       FStar_SMTEncoding_Util.mkForall
                                                         (let _0_426 =
                                                            FStar_SMTEncoding_Util.mkEq
                                                              (app, body)
                                                             in
                                                          ([[app]],
                                                            (FStar_List.append
                                                               vars cvars),
                                                            _0_426))
                                                        in
                                                     (_0_427, a_name, a_name))
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
           ((uu____3795,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____3796;
                          FStar_Syntax_Syntax.lbunivs = uu____3797;
                          FStar_Syntax_Syntax.lbtyp = uu____3798;
                          FStar_Syntax_Syntax.lbeff = uu____3799;
                          FStar_Syntax_Syntax.lbdef = uu____3800;_}::uu____3801),uu____3802)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____3820;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____3822;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____3838 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let _0_428 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (_0_428, [decl_e])))
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
              let uu____3892 = encode_term e1 env  in
              match uu____3892 with
              | (ee1,decls1) ->
                  let uu____3899 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____3899 with
                   | (xs,e2) ->
                       let uu____3913 = FStar_List.hd xs  in
                       (match uu____3913 with
                        | (x,uu____3921) ->
                            let env' = push_term_var env x ee1  in
                            let uu____3923 = encode_body e2 env'  in
                            (match uu____3923 with
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
            let uu____3945 =
              let _0_429 =
                FStar_Syntax_Syntax.null_bv
                  ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                     None FStar_Range.dummyRange)
                 in
              gen_term_var env _0_429  in
            match uu____3945 with
            | (scrsym,scr',env) ->
                let uu____3970 = encode_term e env  in
                (match uu____3970 with
                 | (scr,decls) ->
                     let uu____3977 =
                       let encode_branch b uu____3993 =
                         match uu____3993 with
                         | (else_case,decls) ->
                             let uu____4004 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4004 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p  in
                                  FStar_List.fold_right
                                    (fun uu____4034  ->
                                       fun uu____4035  ->
                                         match (uu____4034, uu____4035) with
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
                                                       fun uu____4072  ->
                                                         match uu____4072
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env)
                                                in
                                             let uu____4077 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____4092 =
                                                     encode_term w env  in
                                                   (match uu____4092 with
                                                    | (w,decls2) ->
                                                        let _0_432 =
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            (let _0_431 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_430
                                                                    =
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                     in
                                                                  (w, _0_430))
                                                                in
                                                             (guard, _0_431))
                                                           in
                                                        (_0_432, decls2))
                                                in
                                             (match uu____4077 with
                                              | (guard,decls2) ->
                                                  let uu____4107 =
                                                    encode_br br env  in
                                                  (match uu____4107 with
                                                   | (br,decls3) ->
                                                       let _0_433 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case)
                                                          in
                                                       (_0_433,
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____3977 with
                      | (match_tm,decls) ->
                          let _0_434 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (_0_434, decls)))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4156 -> let _0_435 = encode_one_pat env pat  in [_0_435]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4166 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____4166
       then
         let _0_436 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" _0_436
       else ());
      (let uu____4168 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____4168 with
       | (vars,pat_term) ->
           let uu____4178 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4201  ->
                     fun v  ->
                       match uu____4201 with
                       | (env,vars) ->
                           let uu____4229 = gen_term_var env v  in
                           (match uu____4229 with
                            | (xx,uu____4241,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, []))
              in
           (match uu____4178 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4288 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_437 = encode_const c  in (scrutinee, _0_437))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____4314 =
                          FStar_TypeChecker_Env.datacons_of_typ env.tcenv
                            tc_name
                           in
                        match uu____4314 with
                        | (uu____4318,uu____4319::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4321 ->
                            mk_data_tester env
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4342  ->
                                  match uu____4342 with
                                  | (arg,uu____4348) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_438 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg _0_438))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4376 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4391 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let _0_440 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4430  ->
                                  match uu____4430 with
                                  | (arg,uu____4439) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_439 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg _0_439))
                         in
                      FStar_All.pipe_right _0_440 FStar_List.flatten
                   in
                let pat_term uu____4457 = encode_term pat_term env  in
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
      let uu____4464 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4479  ->
                fun uu____4480  ->
                  match (uu____4479, uu____4480) with
                  | ((tms,decls),(t,uu____4500)) ->
                      let uu____4511 = encode_term t env  in
                      (match uu____4511 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____4464 with | (l,decls) -> ((FStar_List.rev l), decls)

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
            let uu____4549 = FStar_Syntax_Util.list_elements e  in
            match uu____4549 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____4567 =
              let _0_441 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right _0_441 FStar_Syntax_Util.head_and_args  in
            match uu____4567 with
            | (head,args) ->
                let uu____4607 =
                  let _0_442 =
                    (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                     in
                  (_0_442, args)  in
                (match uu____4607 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____4626,uu____4627)::(e,uu____4629)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4660)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____4681 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements p  in
            let smt_pat_or t =
              let uu____4714 =
                let _0_443 = FStar_Syntax_Util.unmeta t  in
                FStar_All.pipe_right _0_443 FStar_Syntax_Util.head_and_args
                 in
              match uu____4714 with
              | (head,args) ->
                  let uu____4752 =
                    let _0_444 =
                      (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                       in
                    (_0_444, args)  in
                  (match uu____4752 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4770)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____4790 -> None)
               in
            match elts with
            | t::[] ->
                let uu____4808 = smt_pat_or t  in
                (match uu____4808 with
                 | Some e ->
                     let _0_446 = list_elements e  in
                     FStar_All.pipe_right _0_446
                       (FStar_List.map
                          (fun branch  ->
                             let _0_445 = list_elements branch  in
                             FStar_All.pipe_right _0_445
                               (FStar_List.map one_pat)))
                 | uu____4851 ->
                     let _0_447 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [_0_447])
            | uu____4879 ->
                let _0_448 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [_0_448]
             in
          let uu____4905 =
            let uu____4921 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____4921 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4949 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____4949 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____4984;
                            FStar_Syntax_Syntax.effect_name = uu____4985;
                            FStar_Syntax_Syntax.result_typ = uu____4986;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____4988)::(post,uu____4990)::(pats,uu____4992)::[];
                            FStar_Syntax_Syntax.flags = uu____4993;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let _0_449 = lemma_pats pats'  in
                          (binders, pre, post, _0_449)
                      | uu____5038 -> failwith "impos"))
            | uu____5054 -> failwith "Impos"  in
          match uu____4905 with
          | (binders,pre,post,patterns) ->
              let uu____5098 = encode_binders None binders env  in
              (match uu____5098 with
               | (vars,guards,env,decls,uu____5113) ->
                   let uu____5120 =
                     let _0_451 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch  ->
                               let uu____5163 =
                                 let _0_450 =
                                   FStar_All.pipe_right branch
                                     (FStar_List.map
                                        (fun uu____5187  ->
                                           match uu____5187 with
                                           | (t,uu____5194) ->
                                               encode_term t
                                                 (let uu___143_5197 = env  in
                                                  {
                                                    bindings =
                                                      (uu___143_5197.bindings);
                                                    depth =
                                                      (uu___143_5197.depth);
                                                    tcenv =
                                                      (uu___143_5197.tcenv);
                                                    warn =
                                                      (uu___143_5197.warn);
                                                    cache =
                                                      (uu___143_5197.cache);
                                                    nolabels =
                                                      (uu___143_5197.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___143_5197.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right _0_450 FStar_List.unzip
                                  in
                               match uu____5163 with
                               | (pats,decls) -> (pats, decls)))
                        in
                     FStar_All.pipe_right _0_451 FStar_List.unzip  in
                   (match uu____5120 with
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
                                           let _0_453 =
                                             let _0_452 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               _0_452 e
                                              in
                                           _0_453 :: p))
                               | uu____5243 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let _0_454 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e
                                                    in
                                                 _0_454 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let _0_456 =
                                           let _0_455 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             _0_455 tl
                                            in
                                         aux _0_456 vars
                                     | uu____5279 -> pats  in
                                   let _0_457 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux _0_457 vars)
                           in
                        let env =
                          let uu___144_5284 = env  in
                          {
                            bindings = (uu___144_5284.bindings);
                            depth = (uu___144_5284.depth);
                            tcenv = (uu___144_5284.tcenv);
                            warn = (uu___144_5284.warn);
                            cache = (uu___144_5284.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___144_5284.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___144_5284.encode_non_total_function_typ)
                          }  in
                        let uu____5285 =
                          let _0_458 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula _0_458 env  in
                        (match uu____5285 with
                         | (pre,decls'') ->
                             let uu____5292 =
                               let _0_459 = FStar_Syntax_Util.unmeta post  in
                               encode_formula _0_459 env  in
                             (match uu____5292 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let _0_462 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_461 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (let _0_460 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (pre :: guards)
                                               in
                                            (_0_460, post))
                                          in
                                       (pats, vars, _0_461))
                                     in
                                  (_0_462, decls)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug phi =
        let uu____5313 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5313
        then
          let _0_464 = FStar_Syntax_Print.tag_of_term phi  in
          let _0_463 = FStar_Syntax_Print.term_to_string phi  in
          FStar_Util.print2 "Formula (%s)  %s\n" _0_464 _0_463
        else ()  in
      let enc f r l =
        let uu____5340 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5353 = encode_term (Prims.fst x) env  in
                 match uu____5353 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5340 with
        | (decls,args) ->
            let _0_465 =
              let uu___145_5371 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_5371.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_5371.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_465, decls)
         in
      let const_op f r uu____5389 = let _0_466 = f r  in (_0_466, [])  in
      let un_op f l =
        let _0_467 = FStar_List.hd l  in FStar_All.pipe_left f _0_467  in
      let bin_op f uu___117_5419 =
        match uu___117_5419 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5427 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____5454 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5463  ->
                 match uu____5463 with
                 | (t,uu____5471) ->
                     let uu____5472 = encode_formula t env  in
                     (match uu____5472 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l
           in
        match uu____5454 with
        | (decls,phis) ->
            let _0_468 =
              let uu___146_5490 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___146_5490.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___146_5490.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_468, decls)
         in
      let eq_op r uu___118_5505 =
        match uu___118_5505 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r [e1; e2]
        | l -> (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l  in
      let mk_imp r uu___119_5590 =
        match uu___119_5590 with
        | (lhs,uu____5594)::(rhs,uu____5596)::[] ->
            let uu____5617 = encode_formula rhs env  in
            (match uu____5617 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____5626) ->
                      (l1, decls1)
                  | uu____5629 ->
                      let uu____5630 = encode_formula lhs env  in
                      (match uu____5630 with
                       | (l2,decls2) ->
                           let _0_469 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (_0_469, (FStar_List.append decls1 decls2)))))
        | uu____5638 -> failwith "impossible"  in
      let mk_ite r uu___120_5653 =
        match uu___120_5653 with
        | (guard,uu____5657)::(_then,uu____5659)::(_else,uu____5661)::[] ->
            let uu____5690 = encode_formula guard env  in
            (match uu____5690 with
             | (g,decls1) ->
                 let uu____5697 = encode_formula _then env  in
                 (match uu____5697 with
                  | (t,decls2) ->
                      let uu____5704 = encode_formula _else env  in
                      (match uu____5704 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____5713 -> failwith "impossible"  in
      let unboxInt_l f l =
        f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)  in
      let connectives =
        let _0_482 =
          let _0_470 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
          (FStar_Syntax_Const.and_lid, _0_470)  in
        let _0_481 =
          let _0_480 =
            let _0_471 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
            (FStar_Syntax_Const.or_lid, _0_471)  in
          let _0_479 =
            let _0_478 =
              let _0_477 =
                let _0_472 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)
                   in
                (FStar_Syntax_Const.iff_lid, _0_472)  in
              let _0_476 =
                let _0_475 =
                  let _0_474 =
                    let _0_473 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, _0_473)  in
                  [_0_474;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: _0_475  in
              _0_477 :: _0_476  in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: _0_478  in
          _0_480 :: _0_479  in
        _0_482 :: _0_481  in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____5915 = encode_formula phi' env  in
            (match uu____5915 with
             | (phi,decls) ->
                 let _0_483 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r
                    in
                 (_0_483, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____5922 ->
            let _0_484 = FStar_Syntax_Util.unmeta phi  in
            encode_formula _0_484 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____5955 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____5955 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____5963;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____5965;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____5981 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____5981 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head  in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6013::(x,uu____6015)::(t,uu____6017)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6051 = encode_term x env  in
                 (match uu____6051 with
                  | (x,decls) ->
                      let uu____6058 = encode_term t env  in
                      (match uu____6058 with
                       | (t,decls') ->
                           let _0_485 = FStar_SMTEncoding_Term.mk_HasType x t
                              in
                           (_0_485, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6068)::(msg,uu____6070)::(phi,uu____6072)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6106 =
                   let _0_487 =
                     (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
                      in
                   let _0_486 =
                     (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
                      in
                   (_0_487, _0_486)  in
                 (match uu____6106 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6113))) ->
                      let phi =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r
                         in
                      fallback phi
                  | uu____6129 -> fallback phi)
             | uu____6132 when head_redex env head ->
                 let _0_488 = whnf env phi  in encode_formula _0_488 env
             | uu____6140 ->
                 let uu____6148 = encode_term phi env  in
                 (match uu____6148 with
                  | (tt,decls) ->
                      let _0_489 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___147_6155 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___147_6155.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___147_6155.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (_0_489, decls)))
        | uu____6158 ->
            let uu____6159 = encode_term phi env  in
            (match uu____6159 with
             | (tt,decls) ->
                 let _0_490 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___148_6166 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___148_6166.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___148_6166.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (_0_490, decls))
         in
      let encode_q_body env bs ps body =
        let uu____6193 = encode_binders None bs env  in
        match uu____6193 with
        | (vars,guards,env,decls,uu____6215) ->
            let uu____6222 =
              let _0_492 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6257 =
                          let _0_491 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6279  ->
                                    match uu____6279 with
                                    | (t,uu____6285) ->
                                        encode_term t
                                          (let uu___149_6286 = env  in
                                           {
                                             bindings =
                                               (uu___149_6286.bindings);
                                             depth = (uu___149_6286.depth);
                                             tcenv = (uu___149_6286.tcenv);
                                             warn = (uu___149_6286.warn);
                                             cache = (uu___149_6286.cache);
                                             nolabels =
                                               (uu___149_6286.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___149_6286.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right _0_491 FStar_List.unzip  in
                        match uu____6257 with
                        | (p,decls) -> (p, (FStar_List.flatten decls))))
                 in
              FStar_All.pipe_right _0_492 FStar_List.unzip  in
            (match uu____6222 with
             | (pats,decls') ->
                 let uu____6320 = encode_formula body env  in
                 (match uu____6320 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6339;
                             FStar_SMTEncoding_Term.rng = uu____6340;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6348 -> guards  in
                      let _0_493 = FStar_SMTEncoding_Util.mk_and_l guards  in
                      (vars, pats, _0_493, body,
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
                (fun uu____6384  ->
                   match uu____6384 with
                   | (x,uu____6388) ->
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
               let _0_495 = FStar_Syntax_Free.names hd  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let _0_494 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out _0_494) _0_495 tl
                in
             let uu____6398 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6410  ->
                       match uu____6410 with
                       | (b,uu____6414) ->
                           Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
                in
             (match uu____6398 with
              | None  -> ()
              | Some (x,uu____6418) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl
                     in
                  let _0_497 =
                    let _0_496 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      _0_496
                     in
                  FStar_Errors.warn pos _0_497)
          in
       let uu____6428 = FStar_Syntax_Util.destruct_typ_as_formula phi  in
       match uu____6428 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6434 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____6470  ->
                     match uu____6470 with
                     | (l,uu____6480) -> FStar_Ident.lid_equals op l))
              in
           (match uu____6434 with
            | None  -> fallback phi
            | Some (uu____6503,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6532 = encode_q_body env vars pats body  in
             match uu____6532 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let _0_499 =
                     let _0_498 = FStar_SMTEncoding_Util.mkImp (guard, body)
                        in
                     (pats, vars, _0_498)  in
                   FStar_SMTEncoding_Term.mkForall _0_499
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6569 = encode_q_body env vars pats body  in
             match uu____6569 with
             | (vars,pats,guard,body,decls) ->
                 let _0_502 =
                   let _0_501 =
                     let _0_500 = FStar_SMTEncoding_Util.mkAnd (guard, body)
                        in
                     (pats, vars, _0_500)  in
                   FStar_SMTEncoding_Term.mkExists _0_501
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (_0_502, decls))))

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
  let uu____6642 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____6642 with
  | (asym,a) ->
      let uu____6647 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____6647 with
       | (xsym,x) ->
           let uu____6652 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____6652 with
            | (ysym,y) ->
                let quant vars body x =
                  let xname_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_503 =
                         FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                          in
                       (x, _0_503, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  let xtok = Prims.strcat x "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    FStar_SMTEncoding_Util.mkApp
                      (let _0_504 =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                          in
                       (x, _0_504))
                     in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok vars  in
                  let _0_514 =
                    let _0_513 =
                      let _0_512 =
                        let _0_511 =
                          FStar_SMTEncoding_Term.Assume
                            (let _0_506 =
                               FStar_SMTEncoding_Util.mkForall
                                 (let _0_505 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, _0_505))
                                in
                             (_0_506, None,
                               (Some (Prims.strcat "primitive_" x))))
                           in
                        let _0_510 =
                          let _0_509 =
                            FStar_SMTEncoding_Term.Assume
                              (let _0_508 =
                                 FStar_SMTEncoding_Util.mkForall
                                   (let _0_507 =
                                      FStar_SMTEncoding_Util.mkEq
                                        (xtok_app, xapp)
                                       in
                                    ([[xtok_app]], vars, _0_507))
                                  in
                               (_0_508, (Some "Name-token correspondence"),
                                 (Some
                                    (Prims.strcat "token_correspondence_" x))))
                             in
                          [_0_509]  in
                        _0_511 :: _0_510  in
                      xtok_decl :: _0_512  in
                    xname_decl :: _0_513  in
                  (xtok, _0_514)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims =
                  let _0_610 =
                    let _0_517 =
                      let _0_516 =
                        let _0_515 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          _0_515
                         in
                      quant axy _0_516  in
                    (FStar_Syntax_Const.op_Eq, _0_517)  in
                  let _0_609 =
                    let _0_608 =
                      let _0_520 =
                        let _0_519 =
                          let _0_518 =
                            FStar_SMTEncoding_Util.mkNot
                              (FStar_SMTEncoding_Util.mkEq (x, y))
                             in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            _0_518
                           in
                        quant axy _0_519  in
                      (FStar_Syntax_Const.op_notEq, _0_520)  in
                    let _0_607 =
                      let _0_606 =
                        let _0_525 =
                          let _0_524 =
                            let _0_523 =
                              FStar_SMTEncoding_Util.mkLT
                                (let _0_522 =
                                   FStar_SMTEncoding_Term.unboxInt x  in
                                 let _0_521 =
                                   FStar_SMTEncoding_Term.unboxInt y  in
                                 (_0_522, _0_521))
                               in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool _0_523
                             in
                          quant xy _0_524  in
                        (FStar_Syntax_Const.op_LT, _0_525)  in
                      let _0_605 =
                        let _0_604 =
                          let _0_530 =
                            let _0_529 =
                              let _0_528 =
                                FStar_SMTEncoding_Util.mkLTE
                                  (let _0_527 =
                                     FStar_SMTEncoding_Term.unboxInt x  in
                                   let _0_526 =
                                     FStar_SMTEncoding_Term.unboxInt y  in
                                   (_0_527, _0_526))
                                 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool _0_528
                               in
                            quant xy _0_529  in
                          (FStar_Syntax_Const.op_LTE, _0_530)  in
                        let _0_603 =
                          let _0_602 =
                            let _0_535 =
                              let _0_534 =
                                let _0_533 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_532 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_531 =
                                       FStar_SMTEncoding_Term.unboxInt y  in
                                     (_0_532, _0_531))
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool _0_533
                                 in
                              quant xy _0_534  in
                            (FStar_Syntax_Const.op_GT, _0_535)  in
                          let _0_601 =
                            let _0_600 =
                              let _0_540 =
                                let _0_539 =
                                  let _0_538 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_537 =
                                         FStar_SMTEncoding_Term.unboxInt x
                                          in
                                       let _0_536 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       (_0_537, _0_536))
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool _0_538
                                   in
                                quant xy _0_539  in
                              (FStar_Syntax_Const.op_GTE, _0_540)  in
                            let _0_599 =
                              let _0_598 =
                                let _0_545 =
                                  let _0_544 =
                                    let _0_543 =
                                      FStar_SMTEncoding_Util.mkSub
                                        (let _0_542 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         let _0_541 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         (_0_542, _0_541))
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt _0_543
                                     in
                                  quant xy _0_544  in
                                (FStar_Syntax_Const.op_Subtraction, _0_545)
                                 in
                              let _0_597 =
                                let _0_596 =
                                  let _0_548 =
                                    let _0_547 =
                                      let _0_546 =
                                        FStar_SMTEncoding_Util.mkMinus
                                          (FStar_SMTEncoding_Term.unboxInt x)
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt _0_546
                                       in
                                    quant qx _0_547  in
                                  (FStar_Syntax_Const.op_Minus, _0_548)  in
                                let _0_595 =
                                  let _0_594 =
                                    let _0_553 =
                                      let _0_552 =
                                        let _0_551 =
                                          FStar_SMTEncoding_Util.mkAdd
                                            (let _0_550 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 x
                                                in
                                             let _0_549 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 y
                                                in
                                             (_0_550, _0_549))
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          _0_551
                                         in
                                      quant xy _0_552  in
                                    (FStar_Syntax_Const.op_Addition, _0_553)
                                     in
                                  let _0_593 =
                                    let _0_592 =
                                      let _0_558 =
                                        let _0_557 =
                                          let _0_556 =
                                            FStar_SMTEncoding_Util.mkMul
                                              (let _0_555 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   x
                                                  in
                                               let _0_554 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   y
                                                  in
                                               (_0_555, _0_554))
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            _0_556
                                           in
                                        quant xy _0_557  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        _0_558)
                                       in
                                    let _0_591 =
                                      let _0_590 =
                                        let _0_563 =
                                          let _0_562 =
                                            let _0_561 =
                                              FStar_SMTEncoding_Util.mkDiv
                                                (let _0_560 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     x
                                                    in
                                                 let _0_559 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     y
                                                    in
                                                 (_0_560, _0_559))
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              _0_561
                                             in
                                          quant xy _0_562  in
                                        (FStar_Syntax_Const.op_Division,
                                          _0_563)
                                         in
                                      let _0_589 =
                                        let _0_588 =
                                          let _0_568 =
                                            let _0_567 =
                                              let _0_566 =
                                                FStar_SMTEncoding_Util.mkMod
                                                  (let _0_565 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       x
                                                      in
                                                   let _0_564 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       y
                                                      in
                                                   (_0_565, _0_564))
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                _0_566
                                               in
                                            quant xy _0_567  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            _0_568)
                                           in
                                        let _0_587 =
                                          let _0_586 =
                                            let _0_573 =
                                              let _0_572 =
                                                let _0_571 =
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    (let _0_570 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         x
                                                        in
                                                     let _0_569 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         y
                                                        in
                                                     (_0_570, _0_569))
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  _0_571
                                                 in
                                              quant xy _0_572  in
                                            (FStar_Syntax_Const.op_And,
                                              _0_573)
                                             in
                                          let _0_585 =
                                            let _0_584 =
                                              let _0_578 =
                                                let _0_577 =
                                                  let _0_576 =
                                                    FStar_SMTEncoding_Util.mkOr
                                                      (let _0_575 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           x
                                                          in
                                                       let _0_574 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           y
                                                          in
                                                       (_0_575, _0_574))
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    _0_576
                                                   in
                                                quant xy _0_577  in
                                              (FStar_Syntax_Const.op_Or,
                                                _0_578)
                                               in
                                            let _0_583 =
                                              let _0_582 =
                                                let _0_581 =
                                                  let _0_580 =
                                                    let _0_579 =
                                                      FStar_SMTEncoding_Util.mkNot
                                                        (FStar_SMTEncoding_Term.unboxBool
                                                           x)
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      _0_579
                                                     in
                                                  quant qx _0_580  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  _0_581)
                                                 in
                                              [_0_582]  in
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
                        _0_604 :: _0_603  in
                      _0_606 :: _0_605  in
                    _0_608 :: _0_607  in
                  _0_610 :: _0_609  in
                let mk l v =
                  let _0_612 =
                    let _0_611 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____6998  ->
                              match uu____6998 with
                              | (l',uu____7007) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right _0_611
                      (FStar_Option.map
                         (fun uu____7028  ->
                            match uu____7028 with | (uu____7039,b) -> b v))
                     in
                  FStar_All.pipe_right _0_612 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____7073  ->
                          match uu____7073 with
                          | (l',uu____7082) -> FStar_Ident.lid_equals l l'))
                   in
                { mk; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____7105 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____7105 with
      | (xxsym,xx) ->
          let uu____7110 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____7110 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               FStar_SMTEncoding_Term.Assume
                 (let _0_618 =
                    FStar_SMTEncoding_Util.mkForall
                      (let _0_615 =
                         FStar_SMTEncoding_Util.mkImp
                           (let _0_614 =
                              FStar_SMTEncoding_Util.mkEq
                                (let _0_613 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, _0_613))
                               in
                            (xx_has_type, _0_614))
                          in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         _0_615))
                     in
                  let _0_617 =
                    Some
                      (varops.mk_unique
                         (let _0_616 = FStar_Util.digest_of_string tapp_hash
                             in
                          Prims.strcat "pretyping_" _0_616))
                     in
                  (_0_618, (Some "pretyping"), _0_617)))
  
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
    let _0_625 =
      FStar_SMTEncoding_Term.Assume
        (let _0_619 =
           FStar_SMTEncoding_Term.mk_HasType
             FStar_SMTEncoding_Term.mk_Term_unit tt
            in
         (_0_619, (Some "unit typing"), (Some "unit_typing")))
       in
    let _0_624 =
      let _0_623 =
        FStar_SMTEncoding_Term.Assume
          (let _0_622 =
             mkForall_fuel
               (let _0_621 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_620 =
                       FStar_SMTEncoding_Util.mkEq
                         (x, FStar_SMTEncoding_Term.mk_Term_unit)
                        in
                     (typing_pred, _0_620))
                   in
                ([[typing_pred]], [xx], _0_621))
              in
           (_0_622, (Some "unit inversion"), (Some "unit_inversion")))
         in
      [_0_623]  in
    _0_625 :: _0_624  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_637 =
      FStar_SMTEncoding_Term.Assume
        (let _0_631 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_630 =
                let _0_627 =
                  let _0_626 = FStar_SMTEncoding_Term.boxBool b  in [_0_626]
                   in
                [_0_627]  in
              let _0_629 =
                let _0_628 = FStar_SMTEncoding_Term.boxBool b  in
                FStar_SMTEncoding_Term.mk_HasType _0_628 tt  in
              (_0_630, [bb], _0_629))
            in
         (_0_631, (Some "bool typing"), (Some "bool_typing")))
       in
    let _0_636 =
      let _0_635 =
        FStar_SMTEncoding_Term.Assume
          (let _0_634 =
             mkForall_fuel
               (let _0_633 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_632 =
                       FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                     (typing_pred, _0_632))
                   in
                ([[typing_pred]], [xx], _0_633))
              in
           (_0_634, (Some "bool inversion"), (Some "bool_inversion")))
         in
      [_0_635]  in
    _0_637 :: _0_636  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let _0_644 =
        FStar_SMTEncoding_Util.mkApp
          (let _0_643 =
             let _0_642 =
               let _0_641 =
                 let _0_640 = FStar_SMTEncoding_Term.boxInt a  in
                 let _0_639 =
                   let _0_638 = FStar_SMTEncoding_Term.boxInt b  in [_0_638]
                    in
                 _0_640 :: _0_639  in
               tt :: _0_641  in
             tt :: _0_642  in
           ("Prims.Precedes", _0_643))
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_644  in
    let precedes_y_x =
      let _0_645 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_645  in
    let _0_675 =
      FStar_SMTEncoding_Term.Assume
        (let _0_651 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_650 =
                let _0_647 =
                  let _0_646 = FStar_SMTEncoding_Term.boxInt b  in [_0_646]
                   in
                [_0_647]  in
              let _0_649 =
                let _0_648 = FStar_SMTEncoding_Term.boxInt b  in
                FStar_SMTEncoding_Term.mk_HasType _0_648 tt  in
              (_0_650, [bb], _0_649))
            in
         (_0_651, (Some "int typing"), (Some "int_typing")))
       in
    let _0_674 =
      let _0_673 =
        FStar_SMTEncoding_Term.Assume
          (let _0_654 =
             mkForall_fuel
               (let _0_653 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_652 = FStar_SMTEncoding_Term.mk_tester "BoxInt" x
                        in
                     (typing_pred, _0_652))
                   in
                ([[typing_pred]], [xx], _0_653))
              in
           (_0_654, (Some "int inversion"), (Some "int_inversion")))
         in
      let _0_672 =
        let _0_671 =
          FStar_SMTEncoding_Term.Assume
            (let _0_670 =
               mkForall_fuel
                 (let _0_669 =
                    FStar_SMTEncoding_Util.mkImp
                      (let _0_668 =
                         FStar_SMTEncoding_Util.mk_and_l
                           (let _0_667 =
                              let _0_666 =
                                let _0_665 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_656 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_655 =
                                       FStar_SMTEncoding_Util.mkInteger'
                                         (Prims.parse_int "0")
                                        in
                                     (_0_656, _0_655))
                                   in
                                let _0_664 =
                                  let _0_663 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_658 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       let _0_657 =
                                         FStar_SMTEncoding_Util.mkInteger'
                                           (Prims.parse_int "0")
                                          in
                                       (_0_658, _0_657))
                                     in
                                  let _0_662 =
                                    let _0_661 =
                                      FStar_SMTEncoding_Util.mkLT
                                        (let _0_660 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         let _0_659 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         (_0_660, _0_659))
                                       in
                                    [_0_661]  in
                                  _0_663 :: _0_662  in
                                _0_665 :: _0_664  in
                              typing_pred_y :: _0_666  in
                            typing_pred :: _0_667)
                          in
                       (_0_668, precedes_y_x))
                     in
                  ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                    _0_669))
                in
             (_0_670, (Some "well-founded ordering on nat (alt)"),
               (Some "well-founded-ordering-on-nat")))
           in
        [_0_671]  in
      _0_673 :: _0_672  in
    _0_675 :: _0_674  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_687 =
      FStar_SMTEncoding_Term.Assume
        (let _0_681 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_680 =
                let _0_677 =
                  let _0_676 = FStar_SMTEncoding_Term.boxString b  in
                  [_0_676]  in
                [_0_677]  in
              let _0_679 =
                let _0_678 = FStar_SMTEncoding_Term.boxString b  in
                FStar_SMTEncoding_Term.mk_HasType _0_678 tt  in
              (_0_680, [bb], _0_679))
            in
         (_0_681, (Some "string typing"), (Some "string_typing")))
       in
    let _0_686 =
      let _0_685 =
        FStar_SMTEncoding_Term.Assume
          (let _0_684 =
             mkForall_fuel
               (let _0_683 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_682 =
                       FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                     (typing_pred, _0_682))
                   in
                ([[typing_pred]], [xx], _0_683))
              in
           (_0_684, (Some "string inversion"), (Some "string_inversion")))
         in
      [_0_685]  in
    _0_687 :: _0_686  in
  let mk_ref env reft_name uu____7330 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      FStar_SMTEncoding_Util.mkApp
        (let _0_689 =
           let _0_688 = FStar_SMTEncoding_Util.mkFreeV aa  in [_0_688]  in
         (reft_name, _0_689))
       in
    let refb =
      FStar_SMTEncoding_Util.mkApp
        (let _0_691 =
           let _0_690 = FStar_SMTEncoding_Util.mkFreeV bb  in [_0_690]  in
         (reft_name, _0_691))
       in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let _0_704 =
      FStar_SMTEncoding_Term.Assume
        (let _0_694 =
           mkForall_fuel
             (let _0_693 =
                FStar_SMTEncoding_Util.mkImp
                  (let _0_692 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                      in
                   (typing_pred, _0_692))
                 in
              ([[typing_pred]], [xx; aa], _0_693))
            in
         (_0_694, (Some "ref inversion"), (Some "ref_inversion")))
       in
    let _0_703 =
      let _0_702 =
        FStar_SMTEncoding_Term.Assume
          (let _0_701 =
             let _0_700 =
               let _0_699 =
                 FStar_SMTEncoding_Util.mkImp
                   (let _0_698 =
                      FStar_SMTEncoding_Util.mkAnd
                        (typing_pred, typing_pred_b)
                       in
                    let _0_697 =
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_696 = FStar_SMTEncoding_Util.mkFreeV aa  in
                         let _0_695 = FStar_SMTEncoding_Util.mkFreeV bb  in
                         (_0_696, _0_695))
                       in
                    (_0_698, _0_697))
                  in
               ([[typing_pred; typing_pred_b]], [xx; aa; bb], _0_699)  in
             mkForall_fuel' (Prims.parse_int "2") _0_700  in
           (_0_701, (Some "ref typing is injective"),
             (Some "ref_injectivity")))
         in
      [_0_702]  in
    _0_704 :: _0_703  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let _0_706 =
      FStar_SMTEncoding_Term.Assume
        (let _0_705 =
           FStar_SMTEncoding_Util.mkIff
             (FStar_SMTEncoding_Util.mkFalse, valid)
            in
         (_0_705, (Some "False interpretation"), (Some "false_interp")))
       in
    [_0_706]  in
  let mk_and_interp env conj uu____7415 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_708 =
           let _0_707 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
           [_0_707]  in
         ("Valid", _0_708))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_712 =
      FStar_SMTEncoding_Term.Assume
        (let _0_711 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_710 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_709 =
                     FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                   (_0_709, valid))
                 in
              ([[valid]], [aa; bb], _0_710))
            in
         (_0_711, (Some "/\\ interpretation"), (Some "l_and-interp")))
       in
    [_0_712]  in
  let mk_or_interp env disj uu____7455 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_714 =
           let _0_713 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
           [_0_713]  in
         ("Valid", _0_714))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_718 =
      FStar_SMTEncoding_Term.Assume
        (let _0_717 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_716 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_715 =
                     FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                   (_0_715, valid))
                 in
              ([[valid]], [aa; bb], _0_716))
            in
         (_0_717, (Some "\\/ interpretation"), (Some "l_or-interp")))
       in
    [_0_718]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let y = FStar_SMTEncoding_Util.mkFreeV yy  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_720 =
           let _0_719 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y])  in
           [_0_719]  in
         ("Valid", _0_720))
       in
    let _0_724 =
      FStar_SMTEncoding_Term.Assume
        (let _0_723 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_722 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_721 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_721, valid))
                 in
              ([[valid]], [aa; xx; yy], _0_722))
            in
         (_0_723, (Some "Eq2 interpretation"), (Some "eq2-interp")))
       in
    [_0_724]  in
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
        (let _0_726 =
           let _0_725 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y])  in
           [_0_725]  in
         ("Valid", _0_726))
       in
    let _0_730 =
      FStar_SMTEncoding_Term.Assume
        (let _0_729 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_728 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_727 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_727, valid))
                 in
              ([[valid]], [aa; bb; xx; yy], _0_728))
            in
         (_0_729, (Some "Eq3 interpretation"), (Some "eq3-interp")))
       in
    [_0_730]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_732 =
           let _0_731 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
           [_0_731]  in
         ("Valid", _0_732))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_736 =
      FStar_SMTEncoding_Term.Assume
        (let _0_735 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_734 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_733 =
                     FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                   (_0_733, valid))
                 in
              ([[valid]], [aa; bb], _0_734))
            in
         (_0_735, (Some "==> interpretation"), (Some "l_imp-interp")))
       in
    [_0_736]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_738 =
           let _0_737 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
           [_0_737]  in
         ("Valid", _0_738))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_742 =
      FStar_SMTEncoding_Term.Assume
        (let _0_741 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_740 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_739 =
                     FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                   (_0_739, valid))
                 in
              ([[valid]], [aa; bb], _0_740))
            in
         (_0_741, (Some "<==> interpretation"), (Some "l_iff-interp")))
       in
    [_0_742]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_744 =
           let _0_743 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
           [_0_743]  in
         ("Valid", _0_744))
       in
    let not_valid_a =
      let _0_745 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_745  in
    let _0_748 =
      FStar_SMTEncoding_Term.Assume
        (let _0_747 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_746 = FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)
                 in
              ([[valid]], [aa], _0_746))
            in
         (_0_747, (Some "not interpretation"), (Some "l_not-interp")))
       in
    [_0_748]  in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_750 =
           let _0_749 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b])  in
           [_0_749]  in
         ("Valid", _0_750))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_752 =
           let _0_751 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_751]
            in
         ("Valid", _0_752))
       in
    let _0_761 =
      FStar_SMTEncoding_Term.Assume
        (let _0_760 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_759 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_758 =
                     FStar_SMTEncoding_Util.mkForall
                       (let _0_757 =
                          let _0_754 =
                            let _0_753 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_753]  in
                          [_0_754]  in
                        let _0_756 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_755 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_755, valid_b_x))
                           in
                        (_0_757, [xx], _0_756))
                      in
                   (_0_758, valid))
                 in
              ([[valid]], [aa; bb], _0_759))
            in
         (_0_760, (Some "forall interpretation"), (Some "forall-interp")))
       in
    [_0_761]  in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_763 =
           let _0_762 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b])  in
           [_0_762]  in
         ("Valid", _0_763))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_765 =
           let _0_764 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_764]
            in
         ("Valid", _0_765))
       in
    let _0_774 =
      FStar_SMTEncoding_Term.Assume
        (let _0_773 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_772 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_771 =
                     FStar_SMTEncoding_Util.mkExists
                       (let _0_770 =
                          let _0_767 =
                            let _0_766 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_766]  in
                          [_0_767]  in
                        let _0_769 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_768 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_768, valid_b_x))
                           in
                        (_0_770, [xx], _0_769))
                      in
                   (_0_771, valid))
                 in
              ([[valid]], [aa; bb], _0_772))
            in
         (_0_773, (Some "exists interpretation"), (Some "exists-interp")))
       in
    [_0_774]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let _0_777 =
      FStar_SMTEncoding_Term.Assume
        (let _0_776 =
           FStar_SMTEncoding_Term.mk_HasTypeZ
             FStar_SMTEncoding_Term.mk_Range_const range_ty
            in
         let _0_775 = Some (varops.mk_unique "typing_range_const")  in
         (_0_776, (Some "Range_const typing"), _0_775))
       in
    [_0_777]  in
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
          let uu____8068 =
            FStar_Util.find_opt
              (fun uu____8086  ->
                 match uu____8086 with
                 | (l,uu____8096) -> FStar_Ident.lid_equals l t) prims
             in
          match uu____8068 with
          | None  -> []
          | Some (uu____8118,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____8155 = encode_function_type_as_formula None None t env  in
        match uu____8155 with
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
            let uu____8188 =
              (let _0_778 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation _0_778) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____8188
            then
              let uu____8192 = new_term_constant_and_tok_from_lid env lid  in
              match uu____8192 with
              | (vname,vtok,env) ->
                  let arg_sorts =
                    let uu____8204 =
                      (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                       in
                    match uu____8204 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____8207) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____8224  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____8227 -> []  in
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
                  ([d; dd], env)
            else
              (let uu____8236 = prims.is lid  in
               if uu____8236
               then
                 let vname = varops.new_fvar lid  in
                 let uu____8241 = prims.mk lid vname  in
                 match uu____8241 with
                 | (tok,definition) ->
                     let env = push_free_var env lid vname (Some tok)  in
                     (definition, env)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____8256 =
                    let uu____8262 = curried_arrow_formals_comp t_norm  in
                    match uu____8262 with
                    | (args,comp) ->
                        let comp =
                          let uu____8273 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____8273
                          then
                            FStar_Syntax_Syntax.mk_Total
                              (FStar_TypeChecker_Env.reify_comp
                                 (let uu___150_8274 = env.tcenv  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___150_8274.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___150_8274.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___150_8274.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (uu___150_8274.FStar_TypeChecker_Env.gamma);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___150_8274.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___150_8274.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___150_8274.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___150_8274.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___150_8274.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___150_8274.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___150_8274.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___150_8274.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___150_8274.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___150_8274.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___150_8274.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___150_8274.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___150_8274.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___150_8274.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax = true;
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___150_8274.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___150_8274.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___150_8274.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___150_8274.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qname_and_index =
                                      (uu___150_8274.FStar_TypeChecker_Env.qname_and_index)
                                  }) comp FStar_Syntax_Syntax.U_unknown)
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let _0_779 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp
                             in
                          (args, _0_779)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp)))
                     in
                  match uu____8256 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____8304 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____8304 with
                       | (vname,vtok,env) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____8317 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___121_8341  ->
                                     match uu___121_8341 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____8344 =
                                           FStar_Util.prefix vars  in
                                         (match uu____8344 with
                                          | (uu____8355,(xxsym,uu____8357))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let _0_784 =
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_783 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_782 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (let _0_781 =
                                                               let _0_780 =
                                                                 FStar_SMTEncoding_Term.mk_tester
                                                                   (escape
                                                                    d.FStar_Ident.str)
                                                                   xx
                                                                  in
                                                               FStar_All.pipe_left
                                                                 FStar_SMTEncoding_Term.boxBool
                                                                 _0_780
                                                                in
                                                             (vapp, _0_781))
                                                           in
                                                        ([[vapp]], vars,
                                                          _0_782))
                                                      in
                                                   (_0_783,
                                                     (Some
                                                        "Discriminator equation"),
                                                     (Some
                                                        (Prims.strcat
                                                           "disc_equation_"
                                                           (escape
                                                              d.FStar_Ident.str)))))
                                                 in
                                              [_0_784])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____8378 =
                                           FStar_Util.prefix vars  in
                                         (match uu____8378 with
                                          | (uu____8389,(xxsym,uu____8391))
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
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                }  in
                                              let tp_name =
                                                mk_term_projector_name d f
                                                 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx])
                                                 in
                                              let _0_787 =
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_786 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_785 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          _0_785))
                                                      in
                                                   (_0_786,
                                                     (Some
                                                        "Projector equation"),
                                                     (Some
                                                        (Prims.strcat
                                                           "proj_equation_"
                                                           tp_name))))
                                                 in
                                              [_0_787])
                                     | uu____8414 -> []))
                              in
                           let uu____8415 = encode_binders None formals env
                              in
                           (match uu____8415 with
                            | (vars,guards,env',decls1,uu____8431) ->
                                let uu____8438 =
                                  match pre_opt with
                                  | None  ->
                                      let _0_788 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (_0_788, decls1)
                                  | Some p ->
                                      let uu____8444 = encode_formula p env'
                                         in
                                      (match uu____8444 with
                                       | (g,ds) ->
                                           let _0_789 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (_0_789,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____8438 with
                                 | (guard,decls1) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       FStar_SMTEncoding_Util.mkApp
                                         (let _0_790 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars
                                             in
                                          (vname, _0_790))
                                        in
                                     let uu____8462 =
                                       let vname_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (let _0_791 =
                                              FStar_All.pipe_right formals
                                                (FStar_List.map
                                                   (fun uu____8472  ->
                                                      FStar_SMTEncoding_Term.Term_sort))
                                               in
                                            (vname, _0_791,
                                              FStar_SMTEncoding_Term.Term_sort,
                                              None))
                                          in
                                       let uu____8475 =
                                         let env =
                                           let uu___151_8479 = env  in
                                           {
                                             bindings =
                                               (uu___151_8479.bindings);
                                             depth = (uu___151_8479.depth);
                                             tcenv = (uu___151_8479.tcenv);
                                             warn = (uu___151_8479.warn);
                                             cache = (uu___151_8479.cache);
                                             nolabels =
                                               (uu___151_8479.nolabels);
                                             use_zfuel_name =
                                               (uu___151_8479.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____8480 =
                                           Prims.op_Negation
                                             (head_normal env tt)
                                            in
                                         if uu____8480
                                         then
                                           encode_term_pred None tt env
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env
                                             vtok_tm
                                          in
                                       match uu____8475 with
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
                                           let uu____8492 =
                                             match formals with
                                             | [] ->
                                                 let _0_795 =
                                                   let _0_794 =
                                                     let _0_793 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_792  ->
                                                          Some _0_792) _0_793
                                                      in
                                                   push_free_var env lid
                                                     vname _0_794
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing]), _0_795)
                                             | uu____8503 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let _0_796 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     _0_796
                                                    in
                                                 let name_tok_corr =
                                                   FStar_SMTEncoding_Term.Assume
                                                     (let _0_798 =
                                                        FStar_SMTEncoding_Util.mkForall
                                                          (let _0_797 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             _0_797))
                                                         in
                                                      (_0_798,
                                                        (Some
                                                           "Name-token correspondence"),
                                                        (Some
                                                           (Prims.strcat
                                                              "token_correspondence_"
                                                              vname))))
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing]), env)
                                              in
                                           (match uu____8492 with
                                            | (tok_decl,env) ->
                                                ((vname_decl :: tok_decl),
                                                  env))
                                        in
                                     (match uu____8462 with
                                      | (decls2,env) ->
                                          let uu____8533 =
                                            let res_t =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____8538 =
                                              encode_term res_t env'  in
                                            match uu____8538 with
                                            | (encoded_res_t,decls) ->
                                                let _0_799 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, _0_799,
                                                  decls)
                                             in
                                          (match uu____8533 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_801 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        (let _0_800 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           _0_800))
                                                       in
                                                    (_0_801,
                                                      (Some "free var typing"),
                                                      (Some
                                                         (Prims.strcat
                                                            "typing_" vname))))
                                                  in
                                               let freshness =
                                                 let uu____8562 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____8562
                                                 then
                                                   let _0_806 =
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       (let _0_803 =
                                                          FStar_All.pipe_right
                                                            vars
                                                            (FStar_List.map
                                                               Prims.snd)
                                                           in
                                                        let _0_802 =
                                                          varops.next_id ()
                                                           in
                                                        (vname, _0_803,
                                                          FStar_SMTEncoding_Term.Term_sort,
                                                          _0_802))
                                                      in
                                                   let _0_805 =
                                                     let _0_804 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [_0_804]  in
                                                   _0_806 :: _0_805
                                                 else []  in
                                               let g =
                                                 let _0_811 =
                                                   let _0_810 =
                                                     let _0_809 =
                                                       let _0_808 =
                                                         let _0_807 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx :: _0_807
                                                          in
                                                       FStar_List.append
                                                         freshness _0_808
                                                        in
                                                     FStar_List.append decls3
                                                       _0_809
                                                      in
                                                   FStar_List.append decls2
                                                     _0_810
                                                    in
                                                 FStar_List.append decls1
                                                   _0_811
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
          let uu____8593 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8593 with
          | None  ->
              let uu____8616 = encode_free_var env x t t_norm []  in
              (match uu____8616 with
               | (decls,env) ->
                   let uu____8631 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____8631 with
                    | (n,x',uu____8650) -> ((n, x'), decls, env)))
          | Some (n,x,uu____8662) -> ((n, x), [], env)
  
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
          let uu____8695 = encode_free_var env lid t tt quals  in
          match uu____8695 with
          | (decls,env) ->
              let uu____8706 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____8706
              then
                let _0_813 =
                  let _0_812 = encode_smt_lemma env lid tt  in
                  FStar_List.append decls _0_812  in
                (_0_813, env)
              else (decls, env)
  
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
             (fun uu____8736  ->
                fun lb  ->
                  match uu____8736 with
                  | (decls,env) ->
                      let uu____8748 =
                        let _0_814 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env _0_814
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8748 with
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
    fun uu____8775  ->
      fun quals  ->
        match uu____8775 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8824 = FStar_Util.first_N nbinders formals  in
              match uu____8824 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____8864  ->
                         fun uu____8865  ->
                           match (uu____8864, uu____8865) with
                           | ((formal,uu____8875),(binder,uu____8877)) ->
                               FStar_Syntax_Syntax.NT
                                 (let _0_815 =
                                    FStar_Syntax_Syntax.bv_to_name binder  in
                                  (formal, _0_815))) formals binders
                     in
                  let extra_formals =
                    let _0_818 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8902  ->
                              match uu____8902 with
                              | (x,i) ->
                                  let _0_817 =
                                    let uu___152_8909 = x  in
                                    let _0_816 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___152_8909.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___152_8909.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = _0_816
                                    }  in
                                  (_0_817, i)))
                       in
                    FStar_All.pipe_right _0_818
                      FStar_Syntax_Util.name_binders
                     in
                  let body =
                    let _0_824 =
                      let _0_823 =
                        (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
                         in
                      FStar_All.pipe_left (fun _0_822  -> Some _0_822) _0_823
                       in
                    (let _0_821 = FStar_Syntax_Subst.compress body  in
                     let _0_820 =
                       let _0_819 =
                         FStar_Syntax_Util.args_of_binders extra_formals  in
                       FStar_All.pipe_left Prims.snd _0_819  in
                     FStar_Syntax_Syntax.extend_app_n _0_821 _0_820) _0_824
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals), body)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____8953 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____8953
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___153_8954 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___153_8954.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___153_8954.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___153_8954.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___153_8954.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___153_8954.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___153_8954.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___153_8954.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___153_8954.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___153_8954.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___153_8954.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___153_8954.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___153_8954.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___153_8954.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___153_8954.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___153_8954.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___153_8954.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___153_8954.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___153_8954.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___153_8954.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___153_8954.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___153_8954.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___153_8954.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___153_8954.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm t_norm =
                let uu____8975 = FStar_Syntax_Util.abs_formals e  in
                match uu____8975 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____9024::uu____9025 ->
                         let uu____9033 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____9033 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____9058 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____9058 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c  in
                                   let uu____9084 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c)
                                      in
                                   if uu____9084
                                   then
                                     let uu____9102 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____9102 with
                                      | (bs0,rest) ->
                                          let c =
                                            let subst =
                                              FStar_List.map2
                                                (fun uu____9148  ->
                                                   fun uu____9149  ->
                                                     match (uu____9148,
                                                             uu____9149)
                                                     with
                                                     | ((x,uu____9159),
                                                        (b,uu____9161)) ->
                                                         FStar_Syntax_Syntax.NT
                                                           (let _0_825 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                b
                                                               in
                                                            (x, _0_825)))
                                                formals bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst c
                                             in
                                          let body =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let _0_827 =
                                            let _0_826 = get_result_type c
                                               in
                                            (bs0, body, bs0, _0_826)  in
                                          (_0_827, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____9201 =
                                          eta_expand binders formals body
                                            tres
                                           in
                                        match uu____9201 with
                                        | (binders,body) ->
                                            ((binders, body, formals, tres),
                                              false))
                                     else
                                       ((binders, body, formals, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____9253) ->
                              let _0_828 =
                                Prims.fst
                                  (aux norm x.FStar_Syntax_Syntax.sort)
                                 in
                              (_0_828, true)
                          | uu____9278 when Prims.op_Negation norm ->
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
                          | uu____9280 ->
                              failwith
                                (let _0_830 =
                                   FStar_Syntax_Print.term_to_string e  in
                                 let _0_829 =
                                   FStar_Syntax_Print.term_to_string t_norm
                                    in
                                 FStar_Util.format3
                                   "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                   flid.FStar_Ident.str _0_830 _0_829))
                     | uu____9293 ->
                         let uu____9294 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____9294 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____9319 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____9319 with
                               | (formals,c) ->
                                   let tres = get_result_type c  in
                                   let uu____9337 =
                                     eta_expand [] formals e tres  in
                                   (match uu____9337 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____9385 -> (([], e, [], t_norm), false)))
                 in
              aux false t_norm  in
            (try
               let uu____9413 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp))
                  in
               if uu____9413
               then encode_top_level_vals env bindings quals
               else
                 (let uu____9420 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____9461  ->
                            fun lb  ->
                              match uu____9461 with
                              | (toks,typs,decls,env) ->
                                  ((let uu____9512 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____9512
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____9515 =
                                      let _0_831 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env _0_831
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____9515 with
                                    | (tok,decl,env) ->
                                        let _0_834 =
                                          let _0_833 =
                                            let _0_832 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (_0_832, tok)  in
                                          _0_833 :: toks  in
                                        (_0_834, (t_norm :: typs), (decl ::
                                          decls), env)))) ([], [], [], env))
                     in
                  match uu____9420 with
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
                        | uu____9648 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok -> mk_Apply ftok vars
                               | None  ->
                                   let _0_835 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply _0_835 vars)
                            else
                              FStar_SMTEncoding_Util.mkApp
                                (let _0_836 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, _0_836))
                         in
                      let uu____9657 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___122_9659  ->
                                 match uu___122_9659 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9660 -> false)))
                          ||
                          (FStar_All.pipe_right typs
                             (FStar_Util.for_some
                                (fun t  ->
                                   let _0_837 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     _0_837)))
                         in
                      if uu____9657
                      then (decls, env)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs, toks) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____9682;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____9684;
                                FStar_Syntax_Syntax.lbeff = uu____9685;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____9726 =
                                 FStar_Syntax_Subst.univ_var_opening uvs  in
                               (match uu____9726 with
                                | (univ_subst,univ_vars) ->
                                    let env' =
                                      let uu___156_9741 = env  in
                                      let _0_838 =
                                        FStar_TypeChecker_Env.push_univ_vars
                                          env.tcenv univ_vars
                                         in
                                      {
                                        bindings = (uu___156_9741.bindings);
                                        depth = (uu___156_9741.depth);
                                        tcenv = _0_838;
                                        warn = (uu___156_9741.warn);
                                        cache = (uu___156_9741.cache);
                                        nolabels = (uu___156_9741.nolabels);
                                        use_zfuel_name =
                                          (uu___156_9741.use_zfuel_name);
                                        encode_non_total_function_typ =
                                          (uu___156_9741.encode_non_total_function_typ)
                                      }  in
                                    let t_norm =
                                      FStar_Syntax_Subst.subst univ_subst
                                        t_norm
                                       in
                                    let e =
                                      FStar_Syntax_Subst.compress
                                        (FStar_Syntax_Subst.subst univ_subst
                                           e)
                                       in
                                    let uu____9744 =
                                      destruct_bound_function flid t_norm e
                                       in
                                    (match uu____9744 with
                                     | ((binders,body,uu____9756,uu____9757),curry)
                                         ->
                                         ((let uu____9764 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____9764
                                           then
                                             let _0_840 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let _0_839 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               _0_840 _0_839
                                           else ());
                                          (let uu____9766 =
                                             encode_binders None binders env'
                                              in
                                           match uu____9766 with
                                           | (vars,guards,env',binder_decls,uu____9782)
                                               ->
                                               let body =
                                                 let uu____9790 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'.tcenv t_norm
                                                    in
                                                 if uu____9790
                                                 then
                                                   reify_body env'.tcenv body
                                                 else body  in
                                               let app =
                                                 mk_app curry f ftok vars  in
                                               let uu____9793 =
                                                 let uu____9798 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____9798
                                                 then
                                                   let _0_842 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let _0_841 =
                                                     encode_formula body env'
                                                      in
                                                   (_0_842, _0_841)
                                                 else
                                                   (let _0_843 =
                                                      encode_term body env'
                                                       in
                                                    (app, _0_843))
                                                  in
                                               (match uu____9793 with
                                                | (app,(body,decls2)) ->
                                                    let eqn =
                                                      FStar_SMTEncoding_Term.Assume
                                                        (let _0_846 =
                                                           FStar_SMTEncoding_Util.mkForall
                                                             (let _0_844 =
                                                                FStar_SMTEncoding_Util.mkEq
                                                                  (app, body)
                                                                 in
                                                              ([[app]], vars,
                                                                _0_844))
                                                            in
                                                         let _0_845 =
                                                           Some
                                                             (FStar_Util.format1
                                                                "Equation for %s"
                                                                flid.FStar_Ident.str)
                                                            in
                                                         (_0_846, _0_845,
                                                           (Some
                                                              (Prims.strcat
                                                                 "equation_"
                                                                 f))))
                                                       in
                                                    let _0_851 =
                                                      let _0_850 =
                                                        let _0_849 =
                                                          let _0_848 =
                                                            let _0_847 =
                                                              primitive_type_axioms
                                                                env.tcenv
                                                                flid f app
                                                               in
                                                            FStar_List.append
                                                              [eqn] _0_847
                                                             in
                                                          FStar_List.append
                                                            decls2 _0_848
                                                           in
                                                        FStar_List.append
                                                          binder_decls _0_849
                                                         in
                                                      FStar_List.append decls
                                                        _0_850
                                                       in
                                                    (_0_851, env))))))
                           | uu____9826 -> failwith "Impossible")
                        else
                          (let fuel =
                             let _0_852 = varops.fresh "fuel"  in
                             (_0_852, FStar_SMTEncoding_Term.Fuel_sort)  in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env  in
                           let uu____9847 =
                             FStar_All.pipe_right toks
                               (FStar_List.fold_left
                                  (fun uu____9886  ->
                                     fun uu____9887  ->
                                       match (uu____9886, uu____9887) with
                                       | ((gtoks,env),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             varops.new_fvar
                                               (FStar_Ident.lid_add_suffix
                                                  flid "fuel_instrumented")
                                              in
                                           let gtok =
                                             varops.new_fvar
                                               (FStar_Ident.lid_add_suffix
                                                  flid
                                                  "fuel_instrumented_token")
                                              in
                                           let env =
                                             let _0_855 =
                                               let _0_854 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_853  -> Some _0_853)
                                                 _0_854
                                                in
                                             push_free_var env flid gtok
                                               _0_855
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env)) ([], env))
                              in
                           match uu____9847 with
                           | (gtoks,env) ->
                               let gtoks = FStar_List.rev gtoks  in
                               let encode_one_binding env0 uu____10054 t_norm
                                 uu____10056 =
                                 match (uu____10054, uu____10056) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____10081;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____10082;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____10099 =
                                       FStar_Syntax_Subst.univ_var_opening
                                         uvs
                                        in
                                     (match uu____10099 with
                                      | (univ_subst,univ_vars) ->
                                          let env' =
                                            let uu___157_10116 = env  in
                                            let _0_856 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env.tcenv univ_vars
                                               in
                                            {
                                              bindings =
                                                (uu___157_10116.bindings);
                                              depth = (uu___157_10116.depth);
                                              tcenv = _0_856;
                                              warn = (uu___157_10116.warn);
                                              cache = (uu___157_10116.cache);
                                              nolabels =
                                                (uu___157_10116.nolabels);
                                              use_zfuel_name =
                                                (uu___157_10116.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___157_10116.encode_non_total_function_typ)
                                            }  in
                                          let t_norm =
                                            FStar_Syntax_Subst.subst
                                              univ_subst t_norm
                                             in
                                          let e =
                                            FStar_Syntax_Subst.subst
                                              univ_subst e
                                             in
                                          ((let uu____10120 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env0.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____10120
                                            then
                                              let _0_859 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let _0_858 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm
                                                 in
                                              let _0_857 =
                                                FStar_Syntax_Print.term_to_string
                                                  e
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                _0_859 _0_858 _0_857
                                            else ());
                                           (let uu____10122 =
                                              destruct_bound_function flid
                                                t_norm e
                                               in
                                            match uu____10122 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____10144 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env0.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____10144
                                                  then
                                                    let _0_863 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let _0_862 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let _0_861 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let _0_860 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      _0_863 _0_862 _0_861
                                                      _0_860
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____10148 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____10148 with
                                                  | (vars,guards,env',binder_decls,uu____10166)
                                                      ->
                                                      let decl_g =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (let _0_865 =
                                                             let _0_864 =
                                                               FStar_List.map
                                                                 Prims.snd
                                                                 vars
                                                                in
                                                             FStar_SMTEncoding_Term.Fuel_sort
                                                               :: _0_864
                                                              in
                                                           (g, _0_865,
                                                             FStar_SMTEncoding_Term.Term_sort,
                                                             (Some
                                                                "Fuel-instrumented function name")))
                                                         in
                                                      let env0 =
                                                        push_zfuel_name env0
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
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (let _0_866 =
                                                             FStar_List.map
                                                               FStar_SMTEncoding_Util.mkFreeV
                                                               vars
                                                              in
                                                           (f, _0_866))
                                                         in
                                                      let gsapp =
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (let _0_868 =
                                                             let _0_867 =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 ("SFuel",
                                                                   [fuel_tm])
                                                                in
                                                             _0_867 ::
                                                               vars_tm
                                                              in
                                                           (g, _0_868))
                                                         in
                                                      let gmax =
                                                        FStar_SMTEncoding_Util.mkApp
                                                          (let _0_870 =
                                                             let _0_869 =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 ("MaxFuel",
                                                                   [])
                                                                in
                                                             _0_869 ::
                                                               vars_tm
                                                              in
                                                           (g, _0_870))
                                                         in
                                                      let body =
                                                        let uu____10197 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'.tcenv t_norm
                                                           in
                                                        if uu____10197
                                                        then
                                                          reify_body
                                                            env'.tcenv body
                                                        else body  in
                                                      let uu____10199 =
                                                        encode_term body env'
                                                         in
                                                      (match uu____10199 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             FStar_SMTEncoding_Term.Assume
                                                               (let _0_873 =
                                                                  FStar_SMTEncoding_Util.mkForall'
                                                                    (
                                                                    let _0_871
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
                                                                    _0_871))
                                                                   in
                                                                let _0_872 =
                                                                  Some
                                                                    (
                                                                    FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str)
                                                                   in
                                                                (_0_873,
                                                                  _0_872,
                                                                  (Some
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))))
                                                              in
                                                           let eqn_f =
                                                             FStar_SMTEncoding_Term.Assume
                                                               (let _0_875 =
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    (
                                                                    let _0_874
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_874))
                                                                   in
                                                                (_0_875,
                                                                  (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                  (Some
                                                                    (Prims.strcat
                                                                    "fuel_correspondence_"
                                                                    g))))
                                                              in
                                                           let eqn_g' =
                                                             FStar_SMTEncoding_Term.Assume
                                                               (let _0_880 =
                                                                  FStar_SMTEncoding_Util.mkForall
                                                                    (
                                                                    let _0_879
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (let _0_878
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (let _0_877
                                                                    =
                                                                    let _0_876
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    _0_876 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_877))
                                                                     in
                                                                    (gsapp,
                                                                    _0_878))
                                                                     in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_879))
                                                                   in
                                                                (_0_880,
                                                                  (Some
                                                                    "Fuel irrelevance"),
                                                                  (Some
                                                                    (Prims.strcat
                                                                    "fuel_irrelevance_"
                                                                    g))))
                                                              in
                                                           let uu____10243 =
                                                             let uu____10248
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env0
                                                                in
                                                             match uu____10248
                                                             with
                                                             | (vars,v_guards,env,binder_decls,uu____10265)
                                                                 ->
                                                                 let vars_tm
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars
                                                                    in
                                                                 let gapp =
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
                                                                    let _0_881
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    _0_881
                                                                    (fuel ::
                                                                    vars)  in
                                                                   FStar_SMTEncoding_Term.Assume
                                                                    (let _0_883
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_882))
                                                                     in
                                                                    (_0_883,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))))
                                                                    in
                                                                 let uu____10293
                                                                   =
                                                                   let uu____10297
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env gapp
                                                                     in
                                                                   match uu____10297
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let _0_888
                                                                    =
                                                                    let _0_887
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_886
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_885
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_884
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (_0_884,
                                                                    g_typing))
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_885))
                                                                     in
                                                                    (_0_886,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))))  in
                                                                    [_0_887]
                                                                     in
                                                                    (d3,
                                                                    _0_888)
                                                                    in
                                                                 (match uu____10293
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                              in
                                                           (match uu____10243
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
                                                                  env0))))))))
                                  in
                               let uu____10340 =
                                 let _0_889 =
                                   FStar_List.zip3 gtoks typs bindings  in
                                 FStar_List.fold_left
                                   (fun uu____10362  ->
                                      fun uu____10363  ->
                                        match (uu____10362, uu____10363) with
                                        | ((decls,eqns,env0),(gtok,ty,lb)) ->
                                            let uu____10439 =
                                              encode_one_binding env0 gtok ty
                                                lb
                                               in
                                            (match uu____10439 with
                                             | (decls',eqns',env0) ->
                                                 ((decls' :: decls),
                                                   (FStar_List.append eqns'
                                                      eqns), env0)))
                                   ([decls], [], env0) _0_889
                                  in
                               (match uu____10340 with
                                | (decls,eqns,env0) ->
                                    let uu____10485 =
                                      let isDeclFun uu___123_10493 =
                                        match uu___123_10493 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____10494 -> true
                                        | uu____10500 -> false  in
                                      let _0_890 =
                                        FStar_All.pipe_right decls
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right _0_890
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____10485 with
                                     | (prefix_decls,rest) ->
                                         let eqns = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns)),
                                           env0)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let _0_891 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right _0_891 (FStar_String.concat " and ")
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
      (let uu____10557 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____10557
       then
         let _0_892 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _0_892
       else ());
      (let nm =
         let uu____10560 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____10560 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____10563 = encode_sigelt' env se  in
       match uu____10563 with
       | (g,e) ->
           (match g with
            | [] ->
                let _0_894 =
                  let _0_893 =
                    FStar_SMTEncoding_Term.Caption
                      (FStar_Util.format1 "<Skipped %s/>" nm)
                     in
                  [_0_893]  in
                (_0_894, e)
            | uu____10573 ->
                let _0_899 =
                  let _0_898 =
                    let _0_895 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "<Start encoding %s>" nm)
                       in
                    _0_895 :: g  in
                  let _0_897 =
                    let _0_896 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "</end encoding %s>" nm)
                       in
                    [_0_896]  in
                  FStar_List.append _0_898 _0_897  in
                (_0_899, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10581 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____10592) ->
          let uu____10593 =
            let _0_900 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right _0_900 Prims.op_Negation  in
          if uu____10593
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____10613 ->
                   (FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         (let _0_902 =
                            FStar_All.pipe_left (fun _0_901  -> Some _0_901)
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))
                             in
                          ((ed.FStar_Syntax_Syntax.binders), tm, _0_902))))
                     None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env a =
               let uu____10660 =
                 new_term_constant_and_tok_from_lid env
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____10660 with
               | (aname,atok,env) ->
                   let uu____10670 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____10670 with
                    | (formals,uu____10680) ->
                        let uu____10687 =
                          let _0_903 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term _0_903 env  in
                        (match uu____10687 with
                         | (tm,decls) ->
                             let a_decls =
                               let _0_905 =
                                 FStar_SMTEncoding_Term.DeclFun
                                   (let _0_904 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____10705  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, _0_904,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (Some "Action")))
                                  in
                               [_0_905;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____10710 =
                               let aux uu____10739 uu____10740 =
                                 match (uu____10739, uu____10740) with
                                 | ((bv,uu____10767),(env,acc_sorts,acc)) ->
                                     let uu____10788 = gen_term_var env bv
                                        in
                                     (match uu____10788 with
                                      | (xxsym,xx,env) ->
                                          (env,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env, [], [])
                                in
                             (match uu____10710 with
                              | (uu____10826,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_908 =
                                         FStar_SMTEncoding_Util.mkForall
                                           (let _0_907 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (let _0_906 =
                                                   mk_Apply tm xs_sorts  in
                                                 (app, _0_906))
                                               in
                                            ([[app]], xs_sorts, _0_907))
                                          in
                                       (_0_908, (Some "Action equality"),
                                         (Some
                                            (Prims.strcat aname "_equality"))))
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_910 =
                                         FStar_SMTEncoding_Util.mkForall
                                           (let _0_909 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (tok_app, app)
                                               in
                                            ([[tok_app]], xs_sorts, _0_909))
                                          in
                                       (_0_910,
                                         (Some "Action token correspondence"),
                                         (Some
                                            (Prims.strcat aname
                                               "_token_correspondence"))))
                                     in
                                  (env,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____10862 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____10862 with
             | (env,decls2) -> ((FStar_List.flatten decls2), env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10878,uu____10879,uu____10880,uu____10881) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____10884 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____10884 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10895,t,quals,uu____10898) ->
          let will_encode_definition =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___124_10903  ->
                       match uu___124_10903 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _
                           |FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____10906 -> false)))
             in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____10912 = encode_top_level_val env fv t quals  in
             match uu____10912 with
             | (decls,env) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let _0_912 =
                   let _0_911 =
                     primitive_type_axioms env.tcenv lid tname tsym  in
                   FStar_List.append decls _0_911  in
                 (_0_912, env))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____10927,uu____10928) ->
          let uu____10931 = encode_formula f env  in
          (match uu____10931 with
           | (f,decls) ->
               let g =
                 let _0_916 =
                   FStar_SMTEncoding_Term.Assume
                     (let _0_915 =
                        Some
                          (let _0_913 = FStar_Syntax_Print.lid_to_string l
                              in
                           FStar_Util.format1 "Assumption: %s" _0_913)
                         in
                      let _0_914 =
                        Some
                          (varops.mk_unique
                             (Prims.strcat "assumption_" l.FStar_Ident.str))
                         in
                      (f, _0_915, _0_914))
                    in
                 [_0_916]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____10945,quals,uu____10947)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____10955 =
            FStar_Util.fold_map
              (fun env  ->
                 fun lb  ->
                   let lid =
                     ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let uu____10966 =
                     let _0_917 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone _0_917  in
                   if uu____10966
                   then
                     let val_decl =
                       FStar_Syntax_Syntax.Sig_declare_typ
                         (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp), quals, r)
                        in
                     let uu____10981 = encode_sigelt' env val_decl  in
                     match uu____10981 with | (decls,env) -> (env, decls)
                   else (env, [])) env (Prims.snd lbs)
             in
          (match uu____10955 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10998,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                          FStar_Syntax_Syntax.lbunivs = uu____11000;
                          FStar_Syntax_Syntax.lbtyp = uu____11001;
                          FStar_Syntax_Syntax.lbeff = uu____11002;
                          FStar_Syntax_Syntax.lbdef = uu____11003;_}::[]),uu____11004,uu____11005,uu____11006,uu____11007)
          when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid
          ->
          let uu____11023 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____11023 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp
                   (let _0_919 =
                      let _0_918 =
                        FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                      [_0_918]  in
                    ("Valid", _0_919))
                  in
               let decls =
                 let _0_924 =
                   let _0_923 =
                     FStar_SMTEncoding_Term.Assume
                       (let _0_922 =
                          FStar_SMTEncoding_Util.mkForall
                            (let _0_921 =
                               FStar_SMTEncoding_Util.mkEq
                                 (let _0_920 =
                                    FStar_SMTEncoding_Util.mkApp
                                      ("BoxBool_proj_0", [x])
                                     in
                                  (valid_b2t_x, _0_920))
                                in
                             ([[valid_b2t_x]], [xx], _0_921))
                           in
                        (_0_922, (Some "b2t def"), (Some "b2t_def")))
                      in
                   [_0_923]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: _0_924
                  in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____11062,uu____11063,uu____11064,quals,uu____11066) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___125_11074  ->
                  match uu___125_11074 with
                  | FStar_Syntax_Syntax.Discriminator uu____11075 -> true
                  | uu____11076 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____11078,uu____11079,lids,quals,uu____11082) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let _0_925 =
                     (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText  in
                   _0_925 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___126_11092  ->
                     match uu___126_11092 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____11093 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____11096,uu____11097,quals,uu____11099) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___127_11111  ->
                  match uu___127_11111 with
                  | FStar_Syntax_Syntax.Projector uu____11112 -> true
                  | uu____11115 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____11122 = try_lookup_free_var env l  in
          (match uu____11122 with
           | Some uu____11126 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l))
                  in
               encode_sigelt env se)
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
                      (fun uu___128_11181  ->
                         match uu___128_11181 with
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
                           (fun uu___129_11206  ->
                              match uu___129_11206 with
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
                 (fun uu___130_11239  ->
                    match uu___130_11239 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____11240 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____11247 = c  in
              match uu____11247 with
              | (name,args,uu____11251,uu____11252,uu____11253) ->
                  let _0_927 =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_926 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____11263  ->
                                 match uu____11263 with
                                 | (uu____11267,sort,uu____11269) -> sort))
                          in
                       (name, _0_926, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  [_0_927]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____11285 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let _0_928 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right _0_928 FStar_Option.isNone))
               in
            if uu____11285
            then []
            else
              (let uu____11295 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____11295 with
               | (xxsym,xx) ->
                   let uu____11301 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____11312  ->
                             fun l  ->
                               match uu____11312 with
                               | (out,decls) ->
                                   let uu____11324 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____11324 with
                                    | (uu____11330,data_t) ->
                                        let uu____11332 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____11332 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____11361 =
                                                 (FStar_Syntax_Subst.compress
                                                    res).FStar_Syntax_Syntax.n
                                                  in
                                               match uu____11361 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____11367,indices) ->
                                                   indices
                                               | uu____11383 -> []  in
                                             let env =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____11395  ->
                                                         match uu____11395
                                                         with
                                                         | (x,uu____11399) ->
                                                             let _0_930 =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 (let _0_929
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x  in
                                                                  (_0_929,
                                                                    [xx]))
                                                                in
                                                             push_term_var
                                                               env x _0_930)
                                                    env)
                                                in
                                             let uu____11401 =
                                               encode_args indices env  in
                                             (match uu____11401 with
                                              | (indices,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let _0_932 =
                                                        FStar_List.map2
                                                          (fun v  ->
                                                             fun a  ->
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                  (_0_931, a)))
                                                          vars indices
                                                         in
                                                      FStar_All.pipe_right
                                                        _0_932
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let _0_935 =
                                                      FStar_SMTEncoding_Util.mkOr
                                                        (let _0_934 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (let _0_933 =
                                                                mk_data_tester
                                                                  env l xx
                                                                 in
                                                              (_0_933, eqs))
                                                            in
                                                         (out, _0_934))
                                                       in
                                                    (_0_935,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____11301 with
                    | (data_ax,decls) ->
                        let uu____11435 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____11435 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let _0_936 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     _0_936 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               FStar_SMTEncoding_Term.Assume
                                 (let _0_940 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_938 =
                                         add_fuel
                                           (ffsym,
                                             FStar_SMTEncoding_Term.Fuel_sort)
                                           ((xxsym,
                                              FStar_SMTEncoding_Term.Term_sort)
                                           :: vars)
                                          in
                                       let _0_937 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (xx_has_type_sfuel, data_ax)
                                          in
                                       ([[xx_has_type_sfuel]], _0_938,
                                         _0_937))
                                     in
                                  let _0_939 =
                                    Some
                                      (varops.mk_unique
                                         (Prims.strcat
                                            "fuel_guarded_inversion_"
                                            t.FStar_Ident.str))
                                     in
                                  (_0_940, (Some "inversion axiom"), _0_939))
                                in
                             let pattern_guarded_inversion =
                               let uu____11463 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____11463
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let _0_945 =
                                   FStar_SMTEncoding_Term.Assume
                                     (let _0_944 =
                                        FStar_SMTEncoding_Util.mkForall
                                          (let _0_942 =
                                             add_fuel
                                               (ffsym,
                                                 FStar_SMTEncoding_Term.Fuel_sort)
                                               ((xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               :: vars)
                                              in
                                           let _0_941 =
                                             FStar_SMTEncoding_Util.mkImp
                                               (xx_has_type_fuel, data_ax)
                                              in
                                           ([[xx_has_type_fuel;
                                             pattern_guard]], _0_942, _0_941))
                                         in
                                      let _0_943 =
                                        Some
                                          (varops.mk_unique
                                             (Prims.strcat
                                                "pattern_guarded_inversion_"
                                                t.FStar_Ident.str))
                                         in
                                      (_0_944, (Some "inversion axiom"),
                                        _0_943))
                                    in
                                 [_0_945]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____11485 =
            let uu____11493 =
              (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n  in
            match uu____11493 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____11520 -> (tps, k)  in
          (match uu____11485 with
           | (formals,res) ->
               let uu____11535 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11535 with
                | (formals,res) ->
                    let uu____11542 = encode_binders None formals env  in
                    (match uu____11542 with
                     | (vars,guards,env',binder_decls,uu____11557) ->
                         let uu____11564 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____11564 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (let _0_946 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, _0_946))
                                 in
                              let uu____11580 =
                                let tname_decl =
                                  constructor_or_logic_type_decl
                                    (let _0_948 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun uu____11600  ->
                                               match uu____11600 with
                                               | (n,s) ->
                                                   ((Prims.strcat tname n),
                                                     s, false)))
                                        in
                                     let _0_947 = varops.next_id ()  in
                                     (tname, _0_948,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       _0_947, false))
                                   in
                                let uu____11608 =
                                  match vars with
                                  | [] ->
                                      let _0_952 =
                                        let _0_951 =
                                          let _0_950 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_949  -> Some _0_949)
                                            _0_950
                                           in
                                        push_free_var env t tname _0_951  in
                                      ([], _0_952)
                                  | uu____11618 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let _0_953 = varops.next_id ()  in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          _0_953
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        FStar_SMTEncoding_Term.Assume
                                          (let _0_955 =
                                             FStar_SMTEncoding_Util.mkForall'
                                               (let _0_954 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats, None, vars, _0_954))
                                              in
                                           (_0_955,
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
                                match uu____11608 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env)
                                 in
                              (match uu____11580 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____11655 =
                                       encode_term_pred None res env' tapp
                                        in
                                     match uu____11655 with
                                     | (k,decls) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals) >
                                               (Prims.parse_int "0")
                                           then
                                             let _0_958 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_957 =
                                                    let _0_956 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" _0_956
                                                     in
                                                  (_0_957, (Some "kinding"),
                                                    (Some
                                                       (Prims.strcat
                                                          "pre_kinding_" ttok))))
                                                in
                                             [_0_958]
                                           else []  in
                                         let _0_963 =
                                           let _0_962 =
                                             let _0_961 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_960 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      (let _0_959 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k)
                                                          in
                                                       ([[tapp]], vars,
                                                         _0_959))
                                                     in
                                                  (_0_960, None,
                                                    (Some
                                                       (Prims.strcat
                                                          "kinding_" ttok))))
                                                in
                                             [_0_961]  in
                                           FStar_List.append karr _0_962  in
                                         FStar_List.append decls _0_963
                                      in
                                   let aux =
                                     let _0_967 =
                                       let _0_966 =
                                         inversion_axioms tapp vars  in
                                       let _0_965 =
                                         let _0_964 = pretype_axiom tapp vars
                                            in
                                         [_0_964]  in
                                       FStar_List.append _0_966 _0_965  in
                                     FStar_List.append kindingAx _0_967  in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11685,uu____11686,uu____11687,uu____11688,uu____11689,uu____11690,uu____11691)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11698,t,uu____11700,n_tps,quals,uu____11703,drange) ->
          let uu____11709 = new_term_constant_and_tok_from_lid env d  in
          (match uu____11709 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____11720 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____11720 with
                | (formals,t_res) ->
                    let uu____11742 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____11742 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11751 =
                           encode_binders (Some fuel_tm) formals env  in
                         (match uu____11751 with
                          | (vars,guards,env',binder_decls,names) ->
                              let fields =
                                FStar_All.pipe_right names
                                  (FStar_List.mapi
                                     (fun n  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let _0_968 =
                                            mk_term_projector_name d x  in
                                          (_0_968,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let _0_970 =
                                  let _0_969 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort, _0_969,
                                    true)
                                   in
                                FStar_All.pipe_right _0_970
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
                              let uu____11811 =
                                encode_term_pred None t env ddtok_tm  in
                              (match uu____11811 with
                               | (tok_typing,decls3) ->
                                   let uu____11818 =
                                     encode_binders (Some fuel_tm) formals
                                       env
                                      in
                                   (match uu____11818 with
                                    | (vars',guards',env'',decls_formals,uu____11833)
                                        ->
                                        let uu____11840 =
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
                                        (match uu____11840 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11859 ->
                                                   let _0_972 =
                                                     let _0_971 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       _0_971
                                                      in
                                                   [_0_972]
                                                in
                                             let encode_elim uu____11869 =
                                               let uu____11870 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11870 with
                                               | (head,args) ->
                                                   let uu____11899 =
                                                     (FStar_Syntax_Subst.compress
                                                        head).FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11899 with
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
                                                        let uu____11915 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____11915
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv -> fv
                                                                 | uu____11941
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
                                                                    let uu____11949
                                                                    =
                                                                    let _0_973
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv _0_973
                                                                     in
                                                                    if
                                                                    uu____11949
                                                                    then
                                                                    let _0_974
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv xv
                                                                     in
                                                                    [_0_974]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards
                                                                in
                                                             let uu____11954
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____11967
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____11967
                                                                    with
                                                                    | 
                                                                    (env,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____11989
                                                                    =
                                                                    let _0_975
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env
                                                                    _0_975
                                                                     in
                                                                    (match uu____11989
                                                                    with
                                                                    | 
                                                                    (uu____11999,xv,env)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let _0_976
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    _0_976 ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let _0_977
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    _0_977 ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env, (xv
                                                                    ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 encoded_args
                                                                in
                                                             (match uu____11954
                                                              with
                                                              | (uu____12013,arg_vars,elim_eqns_or_guards,uu____12016)
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
                                                                    (let _0_981
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_980
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
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
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
                                                                    "data constructor typing elim"),
                                                                    (Some
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
                                                                    let _0_982
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (_0_982,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_990
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_988
                                                                    =
                                                                    let _0_984
                                                                    =
                                                                    let _0_983
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    [_0_983]
                                                                     in
                                                                    [_0_984]
                                                                     in
                                                                    let _0_987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_986
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let _0_985
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    (_0_986,
                                                                    _0_985))
                                                                     in
                                                                    (_0_988,
                                                                    [x],
                                                                    _0_987))
                                                                     in
                                                                    let _0_989
                                                                    =
                                                                    Some
                                                                    (varops.mk_unique
                                                                    "lextop")
                                                                     in
                                                                    (_0_990,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    _0_989))
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let _0_993
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v  ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let _0_992
                                                                    =
                                                                    let _0_991
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    _0_991
                                                                    dapp  in
                                                                    [_0_992])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    _0_993
                                                                    FStar_List.flatten
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_997
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_996
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_994
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    _0_994))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_996,
                                                                    _0_995))
                                                                     in
                                                                    (_0_997,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)))))
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____12094 ->
                                                        ((let _0_1000 =
                                                            let _0_999 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let _0_998 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              _0_999 _0_998
                                                             in
                                                          FStar_Errors.warn
                                                            drange _0_1000);
                                                         ([], [])))
                                                in
                                             let uu____12098 = encode_elim ()
                                                in
                                             (match uu____12098 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let _0_1021 =
                                                      let _0_1020 =
                                                        let _0_1019 =
                                                          let _0_1018 =
                                                            let _0_1003 =
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                (let _0_1002
                                                                   =
                                                                   Some
                                                                    (let _0_1001
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    _0_1001)
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   _0_1002))
                                                               in
                                                            [_0_1003]  in
                                                          let _0_1017 =
                                                            let _0_1016 =
                                                              let _0_1015 =
                                                                let _0_1014 =
                                                                  let _0_1013
                                                                    =
                                                                    let _0_1012
                                                                    =
                                                                    let _0_1011
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1005
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1004
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_1004))
                                                                     in
                                                                    (_0_1005,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))))
                                                                     in
                                                                    let _0_1010
                                                                    =
                                                                    let _0_1009
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1008
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1007
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let _0_1006
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    _0_1007,
                                                                    _0_1006))
                                                                     in
                                                                    (_0_1008,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))))
                                                                     in
                                                                    [_0_1009]
                                                                     in
                                                                    _0_1011
                                                                    ::
                                                                    _0_1010
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
                                                                    _0_1012
                                                                     in
                                                                  FStar_List.append
                                                                    _0_1013
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  _0_1014
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                _0_1015
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              _0_1016
                                                             in
                                                          FStar_List.append
                                                            _0_1018 _0_1017
                                                           in
                                                        FStar_List.append
                                                          decls3 _0_1019
                                                         in
                                                      FStar_List.append
                                                        decls2 _0_1020
                                                       in
                                                    FStar_List.append
                                                      binder_decls _0_1021
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
           (fun uu____12143  ->
              fun se  ->
                match uu____12143 with
                | (g,env) ->
                    let uu____12155 = encode_sigelt env se  in
                    (match uu____12155 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____12191 =
        match uu____12191 with
        | (i,decls,env) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____12209 ->
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
                 ((let uu____12214 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____12214
                   then
                     let _0_1024 = FStar_Syntax_Print.bv_to_string x  in
                     let _0_1023 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let _0_1022 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.print3 "Normalized %s : %s to %s\n" _0_1024
                       _0_1023 _0_1022
                   else ());
                  (let uu____12216 = encode_term t1 env  in
                   match uu____12216 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____12226 =
                         let _0_1027 =
                           let _0_1026 =
                             let _0_1025 = FStar_Util.digest_of_string t_hash
                                in
                             Prims.strcat _0_1025
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" _0_1026  in
                         new_term_constant_from_string env x _0_1027  in
                       (match uu____12226 with
                        | (xxsym,xx,env') ->
                            let t =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____12240 = FStar_Options.log_queries ()
                                 in
                              if uu____12240
                              then
                                Some
                                  (let _0_1030 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let _0_1029 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let _0_1028 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3 "%s : %s (%s)" _0_1030
                                     _0_1029 _0_1028)
                              else None  in
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____12254,t)) ->
                 let t_norm = whnf env t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____12263 = encode_free_var env fv t t_norm []  in
                 (match uu____12263 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____12282 = encode_sigelt env se  in
                 (match uu____12282 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____12292 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____12292 with | (uu____12304,decls,env) -> (decls, env)
  
let encode_labels labs =
  let prefix =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____12349  ->
            match uu____12349 with
            | (l,uu____12356,uu____12357) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____12378  ->
            match uu____12378 with
            | (l,uu____12386,uu____12387) ->
                let _0_1034 =
                  FStar_All.pipe_left
                    (fun _0_1031  -> FStar_SMTEncoding_Term.Echo _0_1031)
                    (Prims.fst l)
                   in
                let _0_1033 =
                  let _0_1032 =
                    FStar_SMTEncoding_Term.Eval
                      (FStar_SMTEncoding_Util.mkFreeV l)
                     in
                  [_0_1032]  in
                _0_1034 :: _0_1033))
     in
  (prefix, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let _0_1037 =
      let _0_1036 =
        let _0_1035 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = _0_1035;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [_0_1036]  in
    FStar_ST.write last_env _0_1037
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____12413 = FStar_ST.read last_env  in
    match uu____12413 with
    | [] -> failwith "No env; call init first!"
    | e::uu____12419 ->
        let uu___158_12421 = e  in
        {
          bindings = (uu___158_12421.bindings);
          depth = (uu___158_12421.depth);
          tcenv;
          warn = (uu___158_12421.warn);
          cache = (uu___158_12421.cache);
          nolabels = (uu___158_12421.nolabels);
          use_zfuel_name = (uu___158_12421.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___158_12421.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____12425 = FStar_ST.read last_env  in
    match uu____12425 with
    | [] -> failwith "Empty env stack"
    | uu____12430::tl -> FStar_ST.write last_env (env :: tl)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____12438  ->
    let uu____12439 = FStar_ST.read last_env  in
    match uu____12439 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache  in
        let top =
          let uu___159_12460 = hd  in
          {
            bindings = (uu___159_12460.bindings);
            depth = (uu___159_12460.depth);
            tcenv = (uu___159_12460.tcenv);
            warn = (uu___159_12460.warn);
            cache = refs;
            nolabels = (uu___159_12460.nolabels);
            use_zfuel_name = (uu___159_12460.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___159_12460.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd :: tl)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____12466  ->
    let uu____12467 = FStar_ST.read last_env  in
    match uu____12467 with
    | [] -> failwith "Popping an empty stack"
    | uu____12472::tl -> FStar_ST.write last_env tl
  
let mark_env : Prims.unit -> Prims.unit = fun uu____12480  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____12483  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____12486  ->
    let uu____12487 = FStar_ST.read last_env  in
    match uu____12487 with
    | hd::uu____12493::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____12499 -> failwith "Impossible"
  
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
        let uu____12544 = FStar_Options.log_queries ()  in
        if uu____12544
        then
          let _0_1040 =
            FStar_SMTEncoding_Term.Caption
              (let _0_1039 =
                 let _0_1038 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                     (FStar_List.map FStar_Syntax_Print.lid_to_string)
                    in
                 FStar_All.pipe_right _0_1038 (FStar_String.concat ", ")  in
               Prims.strcat "encoding sigelt " _0_1039)
             in
          _0_1040 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____12551 = encode_sigelt env se  in
      match uu____12551 with
      | (decls,env) ->
          (set_env env; FStar_SMTEncoding_Z3.giveZ3 (caption decls))
  
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
      (let uu____12566 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____12566
       then
         let _0_1041 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           _0_1041
       else ());
      (let env = get_env tcenv  in
       let uu____12571 =
         encode_signature
           (let uu___160_12575 = env  in
            {
              bindings = (uu___160_12575.bindings);
              depth = (uu___160_12575.depth);
              tcenv = (uu___160_12575.tcenv);
              warn = false;
              cache = (uu___160_12575.cache);
              nolabels = (uu___160_12575.nolabels);
              use_zfuel_name = (uu___160_12575.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_12575.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____12571 with
       | (decls,env) ->
           let caption decls =
             let uu____12587 = FStar_Options.log_queries ()  in
             if uu____12587
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls  in
           (set_env
              (let uu___161_12592 = env  in
               {
                 bindings = (uu___161_12592.bindings);
                 depth = (uu___161_12592.depth);
                 tcenv = (uu___161_12592.tcenv);
                 warn = true;
                 cache = (uu___161_12592.cache);
                 nolabels = (uu___161_12592.nolabels);
                 use_zfuel_name = (uu___161_12592.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_12592.encode_non_total_function_typ)
               });
            (let uu____12594 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____12594
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
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
         let uu____12636 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____12657 = aux rest  in
                 (match uu____12657 with
                  | (out,rest) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort
                         in
                      let _0_1043 =
                        let _0_1042 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_12675 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_12675.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_12675.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             })
                           in
                        _0_1042 :: out  in
                      (_0_1043, rest))
             | uu____12676 -> ([], bindings)  in
           let uu____12680 = aux bindings  in
           match uu____12680 with
           | (closing,bindings) ->
               let _0_1044 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q
                  in
               (_0_1044, bindings)
            in
         match uu____12636 with
         | (q,bindings) ->
             let uu____12706 =
               let _0_1045 =
                 FStar_List.filter
                   (fun uu___131_12709  ->
                      match uu___131_12709 with
                      | FStar_TypeChecker_Env.Binding_sig uu____12710 ->
                          false
                      | uu____12714 -> true) bindings
                  in
               encode_env_bindings env _0_1045  in
             (match uu____12706 with
              | (env_decls,env) ->
                  ((let uu____12725 =
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
                    if uu____12725
                    then
                      let _0_1046 = FStar_Syntax_Print.term_to_string q  in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        _0_1046
                    else ());
                   (let uu____12727 = encode_formula q env  in
                    match uu____12727 with
                    | (phi,qdecls) ->
                        let uu____12739 =
                          let _0_1047 = FStar_TypeChecker_Env.get_range tcenv
                             in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg _0_1047 phi
                           in
                        (match uu____12739 with
                         | (labels,phi) ->
                             let uu____12751 = encode_labels labels  in
                             (match uu____12751 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_1049 =
                                         FStar_SMTEncoding_Util.mkNot phi  in
                                       let _0_1048 =
                                         Some (varops.mk_unique "@query")  in
                                       (_0_1049, (Some "query"), _0_1048))
                                     in
                                  let suffix =
                                    let _0_1051 =
                                      let _0_1050 =
                                        let uu____12776 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____12776
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append _0_1050
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix _0_1051
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____12789 = encode_formula q env  in
       match uu____12789 with
       | (f,uu____12793) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____12795) -> true
             | uu____12798 -> false)))
  