open Prims
let add_fuel x tl =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
  if uu____16 then tl else x :: tl 
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
      let a =
        let uu___135_98 = a  in
        let _0_298 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = _0_298;
          FStar_Syntax_Syntax.index = (uu___135_98.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___135_98.FStar_Syntax_Syntax.sort)
        }  in
      let _0_299 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape _0_299
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____111 =
          failwith
            (let _0_300 = FStar_Util.string_of_int i  in
             FStar_Util.format2
               "Projector %s on data constructor %s not found" _0_300
               lid.FStar_Ident.str)
           in
        let uu____112 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____112 with
        | (uu____115,t) ->
            let uu____117 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            (match uu____117 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____130 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____130 with
                  | (binders,uu____134) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid (Prims.fst b)))
             | uu____145 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let _0_302 =
        let _0_301 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _0_301  in
      FStar_All.pipe_left escape _0_302
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_303 = mk_term_projector_name lid a  in
         (_0_303,
           (FStar_SMTEncoding_Term.Arrow
              (FStar_SMTEncoding_Term.Term_sort,
                FStar_SMTEncoding_Term.Term_sort))))
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      FStar_SMTEncoding_Util.mkFreeV
        (let _0_304 = mk_term_projector_name_by_pos lid i  in
         (_0_304,
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
  let new_scope uu____353 =
    let _0_306 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let _0_305 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (_0_306, _0_305)  in
  let scopes = FStar_Util.mk_ref (let _0_307 = new_scope ()  in [_0_307])  in
  let mk_unique y =
    let y = escape y  in
    let y =
      let uu____383 =
        let _0_308 = FStar_ST.read scopes  in
        FStar_Util.find_map _0_308
          (fun uu____396  ->
             match uu____396 with
             | (names,uu____403) -> FStar_Util.smap_try_find names y)
         in
      match uu____383 with
      | None  -> y
      | Some uu____408 ->
          (FStar_Util.incr ctr;
           (let _0_310 =
              let _0_309 = FStar_Util.string_of_int (FStar_ST.read ctr)  in
              Prims.strcat "__" _0_309  in
            Prims.strcat y _0_310))
       in
    let top_scope =
      let _0_311 = FStar_List.hd (FStar_ST.read scopes)  in
      FStar_All.pipe_left Prims.fst _0_311  in
    FStar_Util.smap_add top_scope y true; y  in
  let new_var pp rn =
    let _0_314 =
      let _0_313 =
        let _0_312 = FStar_Util.string_of_int rn  in Prims.strcat "__" _0_312
         in
      Prims.strcat pp.FStar_Ident.idText _0_313  in
    FStar_All.pipe_left mk_unique _0_314  in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id uu____450 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh pfx =
    let _0_316 =
      let _0_315 = next_id ()  in
      FStar_All.pipe_left FStar_Util.string_of_int _0_315  in
    FStar_Util.format2 "%s_%s" pfx _0_316  in
  let string_const s =
    let uu____465 =
      let _0_317 = FStar_ST.read scopes  in
      FStar_Util.find_map _0_317
        (fun uu____478  ->
           match uu____478 with
           | (uu____484,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____465 with
    | Some f -> f
    | None  ->
        let id = next_id ()  in
        let f =
          let _0_318 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _0_318  in
        let top_scope =
          let _0_319 = FStar_List.hd (FStar_ST.read scopes)  in
          FStar_All.pipe_left Prims.snd _0_319  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push uu____517 =
    let _0_322 =
      let _0_321 = new_scope ()  in
      let _0_320 = FStar_ST.read scopes  in _0_321 :: _0_320  in
    FStar_ST.write scopes _0_322  in
  let pop uu____539 =
    let _0_323 = FStar_List.tl (FStar_ST.read scopes)  in
    FStar_ST.write scopes _0_323  in
  let mark uu____561 = push ()  in
  let reset_mark uu____565 = pop ()  in
  let commit_mark uu____569 =
    let uu____570 = FStar_ST.read scopes  in
    match uu____570 with
    | (hd1,hd2)::(next1,next2)::tl ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next1 key value) ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v  -> FStar_Util.smap_add next2 key value) ();
         FStar_ST.write scopes ((next1, next2) :: tl))
    | uu____630 -> failwith "Impossible"  in
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
    let uu___136_639 = x  in
    let _0_324 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = _0_324;
      FStar_Syntax_Syntax.index = (uu___136_639.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___136_639.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) 
  | Binding_fvar of (FStar_Ident.lident * Prims.string *
  FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term
  Prims.option) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____660 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____684 -> false
  
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
    let _0_325 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___111_806  ->
              match uu___111_806 with
              | Binding_var (x,uu____808) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____810,uu____811,uu____812) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right _0_325 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t :
  env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option =
  fun env  ->
    fun t  ->
      let uu____844 = FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low
         in
      if uu____844 then Some (FStar_Syntax_Print.term_to_string t) else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let _0_326 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, _0_326)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        let _0_327 = FStar_Util.string_of_int env.depth  in
        Prims.strcat "@x" _0_327  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___137_867 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___137_867.tcenv);
           warn = (uu___137_867.warn);
           cache = (uu___137_867.cache);
           nolabels = (uu___137_867.nolabels);
           use_zfuel_name = (uu___137_867.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___137_867.encode_non_total_function_typ)
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
        (let uu___138_880 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___138_880.depth);
           tcenv = (uu___138_880.tcenv);
           warn = (uu___138_880.warn);
           cache = (uu___138_880.cache);
           nolabels = (uu___138_880.nolabels);
           use_zfuel_name = (uu___138_880.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___138_880.encode_non_total_function_typ)
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
          (let uu___139_896 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___139_896.depth);
             tcenv = (uu___139_896.tcenv);
             warn = (uu___139_896.warn);
             cache = (uu___139_896.cache);
             nolabels = (uu___139_896.nolabels);
             use_zfuel_name = (uu___139_896.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___139_896.encode_non_total_function_typ)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___140_906 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___140_906.depth);
          tcenv = (uu___140_906.tcenv);
          warn = (uu___140_906.warn);
          cache = (uu___140_906.cache);
          nolabels = (uu___140_906.nolabels);
          use_zfuel_name = (uu___140_906.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___140_906.encode_non_total_function_typ)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___112_922  ->
             match uu___112_922 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____930 -> None)
         in
      let uu____933 = aux a  in
      match uu____933 with
      | None  ->
          let a = unmangle a  in
          let uu____940 = aux a  in
          (match uu____940 with
           | None  ->
               failwith
                 (let _0_328 = FStar_Syntax_Print.bv_to_string a  in
                  FStar_Util.format1
                    "Bound term variable not found (after unmangling): %s"
                    _0_328)
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let _0_334 =
        let uu___141_965 = env  in
        let _0_333 =
          let _0_332 =
            Binding_fvar
              (let _0_331 =
                 let _0_330 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                 FStar_All.pipe_left (fun _0_329  -> Some _0_329) _0_330  in
               (x, fname, _0_331, None))
             in
          _0_332 :: (env.bindings)  in
        {
          bindings = _0_333;
          depth = (uu___141_965.depth);
          tcenv = (uu___141_965.tcenv);
          warn = (uu___141_965.warn);
          cache = (uu___141_965.cache);
          nolabels = (uu___141_965.nolabels);
          use_zfuel_name = (uu___141_965.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___141_965.encode_non_total_function_typ)
        }  in
      (fname, ftok, _0_334)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___113_987  ->
           match uu___113_987 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1009 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let _0_335 =
        lookup_binding env
          (fun uu___114_1022  ->
             match uu___114_1022 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1032 -> None)
         in
      FStar_All.pipe_right _0_335 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term Prims.option *
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1044 = try_lookup_lid env a  in
      match uu____1044 with
      | None  ->
          failwith
            (let _0_336 = FStar_Syntax_Print.lid_to_string a  in
             FStar_Util.format1 "Name not found: %s" _0_336)
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
          let uu___142_1091 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___142_1091.depth);
            tcenv = (uu___142_1091.tcenv);
            warn = (uu___142_1091.warn);
            cache = (uu___142_1091.cache);
            nolabels = (uu___142_1091.nolabels);
            use_zfuel_name = (uu___142_1091.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___142_1091.encode_non_total_function_typ)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1103 = lookup_lid env x  in
        match uu____1103 with
        | (t1,t2,uu____1111) ->
            let t3 =
              FStar_SMTEncoding_Util.mkApp
                (let _0_338 =
                   let _0_337 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                      in
                   [_0_337]  in
                 (f, _0_338))
               in
            let uu___143_1119 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___143_1119.depth);
              tcenv = (uu___143_1119.tcenv);
              warn = (uu___143_1119.warn);
              cache = (uu___143_1119.cache);
              nolabels = (uu___143_1119.nolabels);
              use_zfuel_name = (uu___143_1119.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___143_1119.encode_non_total_function_typ)
            }
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1129 = try_lookup_lid env l  in
      match uu____1129 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1156 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1161,fuel::[]) ->
                         let uu____1164 =
                           let _0_340 =
                             let _0_339 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right _0_339 Prims.fst  in
                           FStar_Util.starts_with _0_340 "fuel"  in
                         if uu____1164
                         then
                           let _0_343 =
                             let _0_342 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF _0_342 fuel
                              in
                           FStar_All.pipe_left (fun _0_341  -> Some _0_341)
                             _0_343
                         else Some t
                     | uu____1168 -> Some t)
                | uu____1169 -> None))
  
let lookup_free_var env a =
  let uu____1187 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1187 with
  | Some t -> t
  | None  ->
      failwith
        (let _0_344 =
           FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
         FStar_Util.format1 "Name not found: %s" _0_344)
  
let lookup_free_var_name env a =
  let uu____1206 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1206 with | (x,uu____1213,uu____1214) -> x 
let lookup_free_var_sym env a =
  let uu____1238 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1238 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1259;
             FStar_SMTEncoding_Term.rng = uu____1260;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1268 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym ->
                (match sym.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1282 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___115_1291  ->
           match uu___115_1291 with
           | Binding_fvar (uu____1293,nm',tok,uu____1296) when nm = nm' ->
               tok
           | uu____1301 -> None)
  
let mkForall_fuel' n uu____1318 =
  match uu____1318 with
  | (pats,vars,body) ->
      let fallback uu____1334 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1337 = FStar_Options.unthrottle_inductives ()  in
      if uu____1337
      then fallback ()
      else
        (let uu____1339 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
         match uu____1339 with
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
                       | uu____1358 -> p))
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
                     | uu____1372 ->
                         let _0_345 = add_fuel [guard]  in
                         FStar_All.pipe_right _0_345 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard, body')
               | uu____1374 -> body  in
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
          let _0_346 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_346 FStar_Option.isNone
      | uu____1427 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1434 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
         in
      match uu____1434 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1435,uu____1436,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___116_1465  ->
                  match uu___116_1465 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1466 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1467,uu____1468,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let _0_347 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right _0_347 FStar_Option.isSome
      | uu____1504 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1511 = head_normal env t  in
      if uu____1511
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
    let _0_350 = let _0_348 = FStar_Syntax_Syntax.null_binder t  in [_0_348]
       in
    let _0_349 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs _0_350 _0_349 None
  
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
                    let _0_351 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out _0_351
                | s ->
                    let _0_352 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out _0_352) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___117_1561  ->
    match uu___117_1561 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1562 -> false
  
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
                       FStar_SMTEncoding_Term.freevars = uu____1590;
                       FStar_SMTEncoding_Term.rng = uu____1591;_}::[]),x::xs)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              aux f xs
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1605) ->
              let uu____1610 =
                ((FStar_List.length args) = (FStar_List.length vars)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v
                          | uu____1620 -> false) args vars)
                 in
              if uu____1610 then tok_of_name env f else None
          | (uu____1623,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1626 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        Prims.op_Negation
                          (FStar_Util.for_some
                             (FStar_SMTEncoding_Term.fv_eq fv) vars)))
                 in
              if uu____1626 then Some t else None
          | uu____1630 -> None  in
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
    | uu____1714 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___118_1717  ->
    match uu___118_1717 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        FStar_SMTEncoding_Util.mkApp
          (let _0_354 =
             let _0_353 =
               FStar_SMTEncoding_Term.boxInt
                 (FStar_SMTEncoding_Util.mkInteger'
                    (FStar_Util.int_of_char c))
                in
             [_0_353]  in
           ("FStar.Char.Char", _0_354))
    | FStar_Const.Const_int (i,None ) ->
        FStar_SMTEncoding_Term.boxInt (FStar_SMTEncoding_Util.mkInteger i)
    | FStar_Const.Const_int (i,Some uu____1727) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____1736) ->
        varops.string_const
          (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        failwith
          (let _0_355 = FStar_Syntax_Print.const_to_string c  in
           FStar_Util.format1 "Unhandled constant: %s" _0_355)
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____1760 -> t
        | FStar_Syntax_Syntax.Tm_refine uu____1768 ->
            let _0_356 = FStar_Syntax_Util.unrefine t  in aux true _0_356
        | uu____1773 ->
            if norm
            then let _0_357 = whnf env t  in aux false _0_357
            else
              failwith
                (let _0_359 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let _0_358 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   _0_359 _0_358)
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
    | uu____1795 ->
        let _0_360 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_360)
  
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
        (let uu____1938 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____1938
         then
           let _0_361 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" _0_361
         else ());
        (let uu____1940 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____1976  ->
                   fun b  ->
                     match uu____1976 with
                     | (vars,guards,env,decls,names) ->
                         let uu____2019 =
                           let x = unmangle (Prims.fst b)  in
                           let uu____2028 = gen_term_var env x  in
                           match uu____2028 with
                           | (xxsym,xx,env') ->
                               let uu____2042 =
                                 let _0_362 =
                                   norm env x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt _0_362 env xx  in
                               (match uu____2042 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2019 with
                          | (v,g,env,decls',n) ->
                              ((v :: vars), (g :: guards), env,
                                (FStar_List.append decls decls'), (n ::
                                names)))) ([], [], env, [], []))
            in
         match uu____1940 with
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
          let uu____2132 = encode_term t env  in
          match uu____2132 with
          | (t,decls) ->
              let _0_363 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t  in
              (_0_363, decls)

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
          let uu____2146 = encode_term t env  in
          match uu____2146 with
          | (t,decls) ->
              (match fuel_opt with
               | None  ->
                   let _0_364 = FStar_SMTEncoding_Term.mk_HasTypeZ e t  in
                   (_0_364, decls)
               | Some f ->
                   let _0_365 = FStar_SMTEncoding_Term.mk_HasTypeFuel f e t
                      in
                   (_0_365, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2162 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2162
       then
         let _0_368 = FStar_Syntax_Print.tag_of_term t  in
         let _0_367 = FStar_Syntax_Print.tag_of_term t0  in
         let _0_366 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" _0_368 _0_367 _0_366
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           failwith
             (let _0_372 =
                FStar_All.pipe_left FStar_Range.string_of_range
                  t.FStar_Syntax_Syntax.pos
                 in
              let _0_371 = FStar_Syntax_Print.tag_of_term t0  in
              let _0_370 = FStar_Syntax_Print.term_to_string t0  in
              let _0_369 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _0_372
                _0_371 _0_370 _0_369)
       | FStar_Syntax_Syntax.Tm_bvar x ->
           failwith
             (let _0_373 = FStar_Syntax_Print.bv_to_string x  in
              FStar_Util.format1 "Impossible: locally nameless; got %s"
                _0_373)
       | FStar_Syntax_Syntax.Tm_ascribed (t,k,uu____2174) ->
           encode_term t env
       | FStar_Syntax_Syntax.Tm_meta (t,uu____2194) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t = lookup_term_var env x  in (t, [])
       | FStar_Syntax_Syntax.Tm_fvar v ->
           let _0_374 = lookup_free_var env v.FStar_Syntax_Syntax.fv_name  in
           (_0_374, [])
       | FStar_Syntax_Syntax.Tm_type uu____2208 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t,uu____2211) -> encode_term t env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let _0_375 = encode_const c  in (_0_375, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let uu____2230 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2230 with
            | (binders,res) ->
                let uu____2237 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2237
                then
                  let uu____2240 = encode_binders None binders env  in
                  (match uu____2240 with
                   | (vars,guards,env',decls,uu____2255) ->
                       let fsym =
                         let _0_376 = varops.fresh "f"  in
                         (_0_376, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____2267 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___144_2271 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___144_2271.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___144_2271.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___144_2271.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___144_2271.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___144_2271.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___144_2271.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___144_2271.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___144_2271.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___144_2271.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___144_2271.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___144_2271.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___144_2271.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___144_2271.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___144_2271.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___144_2271.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___144_2271.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___144_2271.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___144_2271.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___144_2271.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___144_2271.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___144_2271.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___144_2271.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___144_2271.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____2267 with
                        | (pre_opt,res_t) ->
                            let uu____2278 =
                              encode_term_pred None res_t env' app  in
                            (match uu____2278 with
                             | (res_pred,decls') ->
                                 let uu____2285 =
                                   match pre_opt with
                                   | None  ->
                                       let _0_377 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (_0_377, [])
                                   | Some pre ->
                                       let uu____2294 =
                                         encode_formula pre env'  in
                                       (match uu____2294 with
                                        | (guard,decls0) ->
                                            let _0_378 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (_0_378, decls0))
                                    in
                                 (match uu____2285 with
                                  | (guards,guard_decls) ->
                                      let t_interp =
                                        FStar_SMTEncoding_Util.mkForall
                                          (let _0_379 =
                                             FStar_SMTEncoding_Util.mkImp
                                               (guards, res_pred)
                                              in
                                           ([[app]], vars, _0_379))
                                         in
                                      let cvars =
                                        let _0_380 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right _0_380
                                          (FStar_List.filter
                                             (fun uu____2323  ->
                                                match uu____2323 with
                                                | (x,uu____2327) ->
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
                                      let uu____2338 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____2338 with
                                       | Some (t',sorts,uu____2354) ->
                                           let _0_382 =
                                             FStar_SMTEncoding_Util.mkApp
                                               (let _0_381 =
                                                  FStar_All.pipe_right cvars
                                                    (FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV)
                                                   in
                                                (t', _0_381))
                                              in
                                           (_0_382, [])
                                       | None  ->
                                           let tsym =
                                             varops.mk_unique
                                               (let _0_383 =
                                                  FStar_Util.digest_of_string
                                                    tkey_hash
                                                   in
                                                Prims.strcat "Tm_arrow_"
                                                  _0_383)
                                              in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let caption =
                                             let uu____2384 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____2384
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
                                               (let _0_384 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    cvars
                                                   in
                                                (tsym, _0_384))
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
                                               (let _0_385 =
                                                  FStar_SMTEncoding_Util.mkForall
                                                    ([[t_has_kind]], cvars,
                                                      t_has_kind)
                                                   in
                                                (_0_385, a_name, a_name))
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
                                               (let _0_389 =
                                                  mkForall_fuel
                                                    (let _0_388 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (let _0_387 =
                                                            let _0_386 =
                                                              FStar_SMTEncoding_Term.mk_PreType
                                                                f
                                                               in
                                                            FStar_SMTEncoding_Term.mk_tester
                                                              "Tm_arrow"
                                                              _0_386
                                                             in
                                                          (f_has_t, _0_387))
                                                        in
                                                     ([[f_has_t]], (fsym ::
                                                       cvars), _0_388))
                                                   in
                                                (_0_389,
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
                                               (let _0_391 =
                                                  FStar_SMTEncoding_Util.mkForall
                                                    (let _0_390 =
                                                       FStar_SMTEncoding_Util.mkIff
                                                         (f_has_t_z,
                                                           t_interp)
                                                        in
                                                     ([[f_has_t_z]], (fsym ::
                                                       cvars), _0_390))
                                                   in
                                                (_0_391, a_name, a_name))
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
                       (let _0_392 =
                          FStar_SMTEncoding_Term.mk_HasType t
                            FStar_SMTEncoding_Term.mk_Term_type
                           in
                        (_0_392, (Some "Typing for non-total arrows"),
                          a_name))
                      in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t  in
                   let t_interp =
                     let a_name = Some (Prims.strcat "pre_typing_" tsym)  in
                     FStar_SMTEncoding_Term.Assume
                       (let _0_396 =
                          mkForall_fuel
                            (let _0_395 =
                               FStar_SMTEncoding_Util.mkImp
                                 (let _0_394 =
                                    let _0_393 =
                                      FStar_SMTEncoding_Term.mk_PreType f  in
                                    FStar_SMTEncoding_Term.mk_tester
                                      "Tm_arrow" _0_393
                                     in
                                  (f_has_t, _0_394))
                                in
                             ([[f_has_t]], [fsym], _0_395))
                           in
                        (_0_396, a_name, a_name))
                      in
                   (t, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2482 ->
           let uu____2487 =
             let uu____2490 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____2490 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2495;
                 FStar_Syntax_Syntax.pos = uu____2496;
                 FStar_Syntax_Syntax.vars = uu____2497;_} ->
                 let uu____2504 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____2504 with
                  | (b,f) ->
                      let _0_397 = Prims.fst (FStar_List.hd b)  in
                      (_0_397, f))
             | uu____2520 -> failwith "impossible"  in
           (match uu____2487 with
            | (x,f) ->
                let uu____2527 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____2527 with
                 | (base_t,decls) ->
                     let uu____2534 = gen_term_var env x  in
                     (match uu____2534 with
                      | (x,xtm,env') ->
                          let uu____2543 = encode_formula f env'  in
                          (match uu____2543 with
                           | (refinement,decls') ->
                               let uu____2550 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____2550 with
                                | (fsym,fterm) ->
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (let _0_398 =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm base_t
                                            in
                                         (_0_398, refinement))
                                       in
                                    let cvars =
                                      let _0_399 =
                                        FStar_SMTEncoding_Term.free_variables
                                          encoding
                                         in
                                      FStar_All.pipe_right _0_399
                                        (FStar_List.filter
                                           (fun uu____2567  ->
                                              match uu____2567 with
                                              | (y,uu____2571) ->
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
                                    let uu____2590 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____2590 with
                                     | Some (t,uu____2605,uu____2606) ->
                                         let _0_401 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (let _0_400 =
                                                FStar_All.pipe_right cvars
                                                  (FStar_List.map
                                                     FStar_SMTEncoding_Util.mkFreeV)
                                                 in
                                              (t, _0_400))
                                            in
                                         (_0_401, [])
                                     | None  ->
                                         let tsym =
                                           varops.mk_unique
                                             (let _0_402 =
                                                FStar_Util.digest_of_string
                                                  tkey_hash
                                                 in
                                              Prims.strcat "Tm_refine_"
                                                _0_402)
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
                                             (let _0_403 =
                                                FStar_List.map
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                  cvars
                                                 in
                                              (tsym, _0_403))
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
                                             (let _0_405 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_404 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (t_haseq_ref,
                                                         t_haseq_base)
                                                      in
                                                   ([[t_haseq_ref]], cvars,
                                                     _0_404))
                                                 in
                                              (_0_405,
                                                (Some
                                                   (Prims.strcat "haseq for "
                                                      tsym)),
                                                (Some
                                                   (Prims.strcat "haseq" tsym))))
                                            in
                                         let t_kinding =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_406 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  ([[t_has_kind]], cvars,
                                                    t_has_kind)
                                                 in
                                              (_0_406,
                                                (Some "refinement kinding"),
                                                (Some
                                                   (Prims.strcat
                                                      "refinement_kinding_"
                                                      tsym))))
                                            in
                                         let t_interp =
                                           FStar_SMTEncoding_Term.Assume
                                             (let _0_409 =
                                                FStar_SMTEncoding_Util.mkForall
                                                  (let _0_407 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (x_has_t, encoding)
                                                      in
                                                   ([[x_has_t]], (ffv :: xfv
                                                     :: cvars), _0_407))
                                                 in
                                              let _0_408 =
                                                Some
                                                  (FStar_Syntax_Print.term_to_string
                                                     t0)
                                                 in
                                              (_0_409, _0_408,
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
           let uu____2708 = encode_term_pred None k env ttm  in
           (match uu____2708 with
            | (t_has_k,decls) ->
                let d =
                  FStar_SMTEncoding_Term.Assume
                    (let _0_412 =
                       Some
                         (varops.mk_unique
                            (let _0_411 =
                               let _0_410 = FStar_Unionfind.uvar_id uv  in
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 _0_410
                                in
                             FStar_Util.format1 "uvar_typing_%s" _0_411))
                        in
                     (t_has_k, (Some "Uvar typing"), _0_412))
                   in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____2722 ->
           let uu____2732 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____2732 with
            | (head,args_e) ->
                let uu____2760 =
                  let _0_413 =
                    (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
                     in
                  (_0_413, args_e)  in
                (match uu____2760 with
                 | (uu____2775,uu____2776) when head_redex env head ->
                     let _0_414 = whnf env t  in encode_term _0_414 env
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
                     let uu____2860 = encode_term v1 env  in
                     (match uu____2860 with
                      | (v1,decls1) ->
                          let uu____2867 = encode_term v2 env  in
                          (match uu____2867 with
                           | (v2,decls2) ->
                               let _0_415 =
                                 FStar_SMTEncoding_Util.mk_LexCons v1 v2  in
                               (_0_415, (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____2875::uu____2876::uu____2877) ->
                     let e0 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_417 =
                                let _0_416 = FStar_List.hd args_e  in
                                [_0_416]  in
                              (head, _0_417)))) None
                         head.FStar_Syntax_Syntax.pos
                        in
                     let e =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_app
                             (let _0_418 = FStar_List.tl args_e  in
                              (e0, _0_418)))) None t0.FStar_Syntax_Syntax.pos
                        in
                     encode_term e env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),(arg,uu____2957)::[]) ->
                     let uu____2975 = encode_term arg env  in
                     (match uu____2975 with
                      | (tm,decls) ->
                          let _0_419 =
                            FStar_SMTEncoding_Util.mkApp ("Reify", [tm])  in
                          (_0_419, decls))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____2983),(arg,uu____2985)::[]) -> encode_term arg env
                 | uu____3003 ->
                     let uu____3011 = encode_args args_e env  in
                     (match uu____3011 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3040 = encode_term head env  in
                            match uu____3040 with
                            | (head,decls') ->
                                let app_tm = mk_Apply_args head args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3071 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3071 with
                                      | (formals,rest) ->
                                          let subst =
                                            FStar_List.map2
                                              (fun uu____3113  ->
                                                 fun uu____3114  ->
                                                   match (uu____3113,
                                                           uu____3114)
                                                   with
                                                   | ((bv,uu____3128),
                                                      (a,uu____3130)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals
                                              args_e
                                             in
                                          let ty =
                                            let _0_420 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right _0_420
                                              (FStar_Syntax_Subst.subst subst)
                                             in
                                          let uu____3144 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3144 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_423 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        ([[has_type]], cvars,
                                                          has_type)
                                                       in
                                                    let _0_422 =
                                                      Some
                                                        (varops.mk_unique
                                                           (let _0_421 =
                                                              FStar_Util.digest_of_string
                                                                (FStar_SMTEncoding_Term.hash_of_term
                                                                   app_tm)
                                                               in
                                                            Prims.strcat
                                                              "partial_app_typing_"
                                                              _0_421))
                                                       in
                                                    (_0_423,
                                                      (Some
                                                         "Partial app typing"),
                                                      _0_422))
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3175 = lookup_free_var_sym env fv  in
                            match uu____3175 with
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
                                  (let _0_424 =
                                     FStar_TypeChecker_Env.lookup_lid
                                       env.tcenv
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   FStar_All.pipe_right _0_424 Prims.snd)
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3219,FStar_Util.Inl t,uu____3221) ->
                                Some t
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3242,FStar_Util.Inr c,uu____3244) ->
                                Some
                                  (FStar_TypeChecker_Env.result_typ env.tcenv
                                     c)
                            | uu____3263 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type ->
                               let head_type =
                                 let _0_425 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine _0_425
                                  in
                               let uu____3281 =
                                 curried_arrow_formals_comp head_type  in
                               (match uu____3281 with
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
                                     | uu____3306 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3349 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____3349 with
            | (bs,body,opening) ->
                let fallback uu____3364 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let _0_426 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (_0_426, [decl])  in
                let is_impure uu___119_3378 =
                  match uu___119_3378 with
                  | FStar_Util.Inl lc ->
                      Prims.op_Negation
                        (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
                  | FStar_Util.Inr (eff,uu____3389) ->
                      let _0_427 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right _0_427 Prims.op_Negation
                   in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc ->
                      let _0_430 =
                        let _0_428 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                           in
                        FStar_Syntax_Subst.subst_comp opening _0_428  in
                      FStar_All.pipe_right _0_430
                        (fun _0_429  -> Some _0_429)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar uu____3426 =
                        let _0_431 =
                          FStar_TypeChecker_Env.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right _0_431 Prims.fst  in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let _0_433 =
                          FStar_Syntax_Syntax.mk_Total (new_uvar ())  in
                        FStar_All.pipe_right _0_433
                          (fun _0_432  -> Some _0_432)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let _0_435 =
                             FStar_Syntax_Syntax.mk_GTotal (new_uvar ())  in
                           FStar_All.pipe_right _0_435
                             (fun _0_434  -> Some _0_434))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let _0_437 =
                         let _0_436 = FStar_Syntax_Print.term_to_string t0
                            in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s"
                           _0_436
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos _0_437);
                      fallback ())
                 | Some lc ->
                     let uu____3456 = is_impure lc  in
                     if uu____3456
                     then fallback ()
                     else
                       (let uu____3460 = encode_binders None bs env  in
                        match uu____3460 with
                        | (vars,guards,envbody,decls,uu____3475) ->
                            let uu____3482 = encode_term body envbody  in
                            (match uu____3482 with
                             | (body,decls') ->
                                 let key_body =
                                   FStar_SMTEncoding_Util.mkForall
                                     (let _0_439 =
                                        FStar_SMTEncoding_Util.mkImp
                                          (let _0_438 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               guards
                                              in
                                           (_0_438, body))
                                         in
                                      ([], vars, _0_439))
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
                                 let uu____3500 =
                                   FStar_Util.smap_try_find env.cache
                                     tkey_hash
                                    in
                                 (match uu____3500 with
                                  | Some (t,uu____3515,uu____3516) ->
                                      let _0_441 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (let _0_440 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               cvars
                                              in
                                           (t, _0_440))
                                         in
                                      (_0_441, [])
                                  | None  ->
                                      let uu____3535 = is_eta env vars body
                                         in
                                      (match uu____3535 with
                                       | Some t -> (t, [])
                                       | None  ->
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars
                                              in
                                           let fsym =
                                             varops.mk_unique
                                               (let _0_442 =
                                                  FStar_Util.digest_of_string
                                                    tkey_hash
                                                   in
                                                Prims.strcat "Tm_abs_" _0_442)
                                              in
                                           let fdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (fsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 None)
                                              in
                                           let f =
                                             FStar_SMTEncoding_Util.mkApp
                                               (let _0_443 =
                                                  FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV
                                                    cvars
                                                   in
                                                (fsym, _0_443))
                                              in
                                           let app = mk_Apply f vars  in
                                           let typing_f =
                                             let uu____3556 = codomain_eff lc
                                                in
                                             match uu____3556 with
                                             | None  -> []
                                             | Some c ->
                                                 let tfun =
                                                   FStar_Syntax_Util.arrow bs
                                                     c
                                                    in
                                                 let uu____3561 =
                                                   encode_term_pred None tfun
                                                     env f
                                                    in
                                                 (match uu____3561 with
                                                  | (f_has_t,decls'') ->
                                                      let a_name =
                                                        Some
                                                          (Prims.strcat
                                                             "typing_" fsym)
                                                         in
                                                      let _0_446 =
                                                        let _0_445 =
                                                          FStar_SMTEncoding_Term.Assume
                                                            (let _0_444 =
                                                               FStar_SMTEncoding_Util.mkForall
                                                                 ([[f]],
                                                                   cvars,
                                                                   f_has_t)
                                                                in
                                                             (_0_444, a_name,
                                                               a_name))
                                                           in
                                                        [_0_445]  in
                                                      FStar_List.append
                                                        decls'' _0_446)
                                              in
                                           let interp_f =
                                             let a_name =
                                               Some
                                                 (Prims.strcat
                                                    "interpretation_" fsym)
                                                in
                                             FStar_SMTEncoding_Term.Assume
                                               (let _0_448 =
                                                  FStar_SMTEncoding_Util.mkForall
                                                    (let _0_447 =
                                                       FStar_SMTEncoding_Util.mkEq
                                                         (app, body)
                                                        in
                                                     ([[app]],
                                                       (FStar_List.append
                                                          vars cvars),
                                                       _0_447))
                                                   in
                                                (_0_448, a_name, a_name))
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
           ((uu____3596,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____3597;
                          FStar_Syntax_Syntax.lbunivs = uu____3598;
                          FStar_Syntax_Syntax.lbtyp = uu____3599;
                          FStar_Syntax_Syntax.lbeff = uu____3600;
                          FStar_Syntax_Syntax.lbdef = uu____3601;_}::uu____3602),uu____3603)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____3621;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____3623;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____3639 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let _0_449 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (_0_449, [decl_e])))
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
              let uu____3693 = encode_term e1 env  in
              match uu____3693 with
              | (ee1,decls1) ->
                  let uu____3700 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____3700 with
                   | (xs,e2) ->
                       let uu____3714 = FStar_List.hd xs  in
                       (match uu____3714 with
                        | (x,uu____3722) ->
                            let env' = push_term_var env x ee1  in
                            let uu____3724 = encode_body e2 env'  in
                            (match uu____3724 with
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
            let uu____3746 = encode_term e env  in
            match uu____3746 with
            | (scr,decls) ->
                let uu____3753 =
                  FStar_List.fold_right
                    (fun b  ->
                       fun uu____3761  ->
                         match uu____3761 with
                         | (else_case,decls) ->
                             let uu____3772 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____3772 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env p  in
                                  FStar_List.fold_right
                                    (fun uu____3802  ->
                                       fun uu____3803  ->
                                         match (uu____3802, uu____3803) with
                                         | ((env0,pattern),(else_case,decls))
                                             ->
                                             let guard = pattern.guard scr
                                                in
                                             let projections =
                                               pattern.projections scr  in
                                             let env =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____3840  ->
                                                         match uu____3840
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env x t) env)
                                                in
                                             let uu____3845 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w ->
                                                   let uu____3860 =
                                                     encode_term w env  in
                                                   (match uu____3860 with
                                                    | (w,decls2) ->
                                                        let _0_452 =
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            (let _0_451 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_450
                                                                    =
                                                                    FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue
                                                                     in
                                                                  (w, _0_450))
                                                                in
                                                             (guard, _0_451))
                                                           in
                                                        (_0_452, decls2))
                                                in
                                             (match uu____3845 with
                                              | (guard,decls2) ->
                                                  let uu____3875 =
                                                    encode_br br env  in
                                                  (match uu____3875 with
                                                   | (br,decls3) ->
                                                       let _0_453 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard, br,
                                                             else_case)
                                                          in
                                                       (_0_453,
                                                         (FStar_List.append
                                                            decls
                                                            (FStar_List.append
                                                               decls2 decls3))))))
                                    patterns (else_case, decls))) pats
                    (default_case, decls)
                   in
                (match uu____3753 with
                 | (match_tm,decls) -> (match_tm, decls))

and encode_pat :
  env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____3906 -> let _0_454 = encode_one_pat env pat  in [_0_454]

and encode_one_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____3916 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____3916
       then
         let _0_455 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" _0_455
       else ());
      (let uu____3918 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____3918 with
       | (vars,pat_term) ->
           let uu____3928 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____3951  ->
                     fun v  ->
                       match uu____3951 with
                       | (env,vars) ->
                           let uu____3979 = gen_term_var env v  in
                           (match uu____3979 with
                            | (xx,uu____3991,env) ->
                                (env,
                                  ((v,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars)))) (env, []))
              in
           (match uu____3928 with
            | (env,vars) ->
                let rec mk_guard pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4038 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_456 = encode_const c  in (scrutinee, _0_456))
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
                                fun uu____4076  ->
                                  match uu____4076 with
                                  | (arg,uu____4082) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_457 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg _0_457))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat scrutinee =
                  match pat.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4110 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4125 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let _0_459 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4164  ->
                                  match uu____4164 with
                                  | (arg,uu____4173) ->
                                      let proj =
                                        primitive_projector_by_pos env.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let _0_458 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg _0_458))
                         in
                      FStar_All.pipe_right _0_459 FStar_List.flatten
                   in
                let pat_term uu____4191 = encode_term pat_term env  in
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
      let uu____4198 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4213  ->
                fun uu____4214  ->
                  match (uu____4213, uu____4214) with
                  | ((tms,decls),(t,uu____4234)) ->
                      let uu____4245 = encode_term t env  in
                      (match uu____4245 with
                       | (t,decls') ->
                           ((t :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____4198 with | (l,decls) -> ((FStar_List.rev l), decls)

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
            let uu____4283 = FStar_Syntax_Util.list_elements e  in
            match uu____4283 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 [])
             in
          let one_pat p =
            let uu____4301 =
              let _0_460 = FStar_Syntax_Util.unmeta p  in
              FStar_All.pipe_right _0_460 FStar_Syntax_Util.head_and_args  in
            match uu____4301 with
            | (head,args) ->
                let uu____4341 =
                  let _0_461 =
                    (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                     in
                  (_0_461, args)  in
                (match uu____4341 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____4360,uu____4361)::(e,uu____4363)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4394)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____4415 -> failwith "Unexpected pattern term")
             in
          let lemma_pats p =
            let elts = list_elements p  in
            let smt_pat_or t =
              let uu____4448 =
                let _0_462 = FStar_Syntax_Util.unmeta t  in
                FStar_All.pipe_right _0_462 FStar_Syntax_Util.head_and_args
                 in
              match uu____4448 with
              | (head,args) ->
                  let uu____4486 =
                    let _0_463 =
                      (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
                       in
                    (_0_463, args)  in
                  (match uu____4486 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____4504)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____4524 -> None)
               in
            match elts with
            | t::[] ->
                let uu____4542 = smt_pat_or t  in
                (match uu____4542 with
                 | Some e ->
                     let _0_465 = list_elements e  in
                     FStar_All.pipe_right _0_465
                       (FStar_List.map
                          (fun branch  ->
                             let _0_464 = list_elements branch  in
                             FStar_All.pipe_right _0_464
                               (FStar_List.map one_pat)))
                 | uu____4585 ->
                     let _0_466 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                     [_0_466])
            | uu____4613 ->
                let _0_467 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                [_0_467]
             in
          let uu____4639 =
            let uu____4655 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            match uu____4655 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4683 = FStar_Syntax_Subst.open_comp binders c  in
                (match uu____4683 with
                 | (binders,c) ->
                     (match c.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_typ_name = uu____4718;
                            FStar_Syntax_Syntax.comp_univs = uu____4719;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____4721)::(post,uu____4723)::(pats,uu____4725)::[];
                            FStar_Syntax_Syntax.flags = uu____4726;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats  in
                          let _0_468 = lemma_pats pats'  in
                          (binders, pre, post, _0_468)
                      | uu____4769 -> failwith "impos"))
            | uu____4785 -> failwith "Impos"  in
          match uu____4639 with
          | (binders,pre,post,patterns) ->
              let uu____4829 = encode_binders None binders env  in
              (match uu____4829 with
               | (vars,guards,env,decls,uu____4844) ->
                   let uu____4851 =
                     let _0_470 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch  ->
                               let uu____4894 =
                                 let _0_469 =
                                   FStar_All.pipe_right branch
                                     (FStar_List.map
                                        (fun uu____4918  ->
                                           match uu____4918 with
                                           | (t,uu____4925) ->
                                               encode_term t
                                                 (let uu___145_4928 = env  in
                                                  {
                                                    bindings =
                                                      (uu___145_4928.bindings);
                                                    depth =
                                                      (uu___145_4928.depth);
                                                    tcenv =
                                                      (uu___145_4928.tcenv);
                                                    warn =
                                                      (uu___145_4928.warn);
                                                    cache =
                                                      (uu___145_4928.cache);
                                                    nolabels =
                                                      (uu___145_4928.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___145_4928.encode_non_total_function_typ)
                                                  })))
                                    in
                                 FStar_All.pipe_right _0_469 FStar_List.unzip
                                  in
                               match uu____4894 with
                               | (pats,decls) -> (pats, decls)))
                        in
                     FStar_All.pipe_right _0_470 FStar_List.unzip  in
                   (match uu____4851 with
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
                                           let _0_472 =
                                             let _0_471 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l
                                                in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               _0_471 e
                                              in
                                           _0_472 :: p))
                               | uu____4974 ->
                                   let rec aux tl vars =
                                     match vars with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let _0_473 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl e
                                                    in
                                                 _0_473 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars
                                         ->
                                         let _0_475 =
                                           let _0_474 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             _0_474 tl
                                            in
                                         aux _0_475 vars
                                     | uu____5010 -> pats  in
                                   let _0_476 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   aux _0_476 vars)
                           in
                        let env =
                          let uu___146_5015 = env  in
                          {
                            bindings = (uu___146_5015.bindings);
                            depth = (uu___146_5015.depth);
                            tcenv = (uu___146_5015.tcenv);
                            warn = (uu___146_5015.warn);
                            cache = (uu___146_5015.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___146_5015.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___146_5015.encode_non_total_function_typ)
                          }  in
                        let uu____5016 =
                          let _0_477 = FStar_Syntax_Util.unmeta pre  in
                          encode_formula _0_477 env  in
                        (match uu____5016 with
                         | (pre,decls'') ->
                             let uu____5023 =
                               let _0_478 = FStar_Syntax_Util.unmeta post  in
                               encode_formula _0_478 env  in
                             (match uu____5023 with
                              | (post,decls''') ->
                                  let decls =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls')
                                         (FStar_List.append decls'' decls'''))
                                     in
                                  let _0_481 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_480 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (let _0_479 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (pre :: guards)
                                               in
                                            (_0_479, post))
                                          in
                                       (pats, vars, _0_480))
                                     in
                                  (_0_481, decls)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug phi =
        let uu____5044 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____5044
        then
          let _0_483 = FStar_Syntax_Print.tag_of_term phi  in
          let _0_482 = FStar_Syntax_Print.term_to_string phi  in
          FStar_Util.print2 "Formula (%s)  %s\n" _0_483 _0_482
        else ()  in
      let enc f r l =
        let uu____5071 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5084 = encode_term (Prims.fst x) env  in
                 match uu____5084 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____5071 with
        | (decls,args) ->
            let _0_484 =
              let uu___147_5102 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___147_5102.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___147_5102.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_484, decls)
         in
      let const_op f r uu____5120 = let _0_485 = f r  in (_0_485, [])  in
      let un_op f l =
        let _0_486 = FStar_List.hd l  in FStar_All.pipe_left f _0_486  in
      let bin_op f uu___120_5150 =
        match uu___120_5150 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5158 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____5185 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5194  ->
                 match uu____5194 with
                 | (t,uu____5202) ->
                     let uu____5203 = encode_formula t env  in
                     (match uu____5203 with
                      | (phi,decls') ->
                          ((FStar_List.append decls decls'), phi))) [] l
           in
        match uu____5185 with
        | (decls,phis) ->
            let _0_487 =
              let uu___148_5221 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___148_5221.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___148_5221.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (_0_487, decls)
         in
      let eq_op r uu___121_5236 =
        match uu___121_5236 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r [e1; e2]
        | l -> (enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l  in
      let mk_imp r uu___122_5321 =
        match uu___122_5321 with
        | (lhs,uu____5325)::(rhs,uu____5327)::[] ->
            let uu____5348 = encode_formula rhs env  in
            (match uu____5348 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____5357) ->
                      (l1, decls1)
                  | uu____5360 ->
                      let uu____5361 = encode_formula lhs env  in
                      (match uu____5361 with
                       | (l2,decls2) ->
                           let _0_488 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (_0_488, (FStar_List.append decls1 decls2)))))
        | uu____5369 -> failwith "impossible"  in
      let mk_ite r uu___123_5384 =
        match uu___123_5384 with
        | (guard,uu____5388)::(_then,uu____5390)::(_else,uu____5392)::[] ->
            let uu____5421 = encode_formula guard env  in
            (match uu____5421 with
             | (g,decls1) ->
                 let uu____5428 = encode_formula _then env  in
                 (match uu____5428 with
                  | (t,decls2) ->
                      let uu____5435 = encode_formula _else env  in
                      (match uu____5435 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____5444 -> failwith "impossible"  in
      let unboxInt_l f l =
        f (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)  in
      let connectives =
        let _0_501 =
          let _0_489 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)  in
          (FStar_Syntax_Const.and_lid, _0_489)  in
        let _0_500 =
          let _0_499 =
            let _0_490 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)  in
            (FStar_Syntax_Const.or_lid, _0_490)  in
          let _0_498 =
            let _0_497 =
              let _0_496 =
                let _0_491 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)
                   in
                (FStar_Syntax_Const.iff_lid, _0_491)  in
              let _0_495 =
                let _0_494 =
                  let _0_493 =
                    let _0_492 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, _0_492)  in
                  [_0_493;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: _0_494  in
              _0_496 :: _0_495  in
            (FStar_Syntax_Const.imp_lid, mk_imp) :: _0_497  in
          _0_499 :: _0_498  in
        _0_501 :: _0_500  in
      let rec fallback phi =
        match phi.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____5646 = encode_formula phi' env  in
            (match uu____5646 with
             | (phi,decls) ->
                 let _0_502 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi, msg, r)) r
                    in
                 (_0_502, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____5653 ->
            let _0_503 = FStar_Syntax_Util.unmeta phi  in
            encode_formula _0_503 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____5686 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____5686 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____5694;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____5696;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____5712 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____5712 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head,args) ->
            let head = FStar_Syntax_Util.un_uinst head  in
            (match ((head.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____5744::(x,uu____5746)::(t,uu____5748)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____5782 = encode_term x env  in
                 (match uu____5782 with
                  | (x,decls) ->
                      let uu____5789 = encode_term t env  in
                      (match uu____5789 with
                       | (t,decls') ->
                           let _0_504 = FStar_SMTEncoding_Term.mk_HasType x t
                              in
                           (_0_504, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____5799)::(msg,uu____5801)::(phi,uu____5803)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____5837 =
                   let _0_506 =
                     (FStar_Syntax_Subst.compress r).FStar_Syntax_Syntax.n
                      in
                   let _0_505 =
                     (FStar_Syntax_Subst.compress msg).FStar_Syntax_Syntax.n
                      in
                   (_0_506, _0_505)  in
                 (match uu____5837 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____5844))) ->
                      let phi =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r,
                                     false))))) None r
                         in
                      fallback phi
                  | uu____5860 -> fallback phi)
             | uu____5863 when head_redex env head ->
                 let _0_507 = whnf env phi  in encode_formula _0_507 env
             | uu____5871 ->
                 let uu____5879 = encode_term phi env  in
                 (match uu____5879 with
                  | (tt,decls) ->
                      let _0_508 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___149_5886 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___149_5886.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___149_5886.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (_0_508, decls)))
        | uu____5889 ->
            let uu____5890 = encode_term phi env  in
            (match uu____5890 with
             | (tt,decls) ->
                 let _0_509 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___150_5897 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___150_5897.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___150_5897.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (_0_509, decls))
         in
      let encode_q_body env bs ps body =
        let uu____5924 = encode_binders None bs env  in
        match uu____5924 with
        | (vars,guards,env,decls,uu____5946) ->
            let uu____5953 =
              let _0_511 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____5988 =
                          let _0_510 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6010  ->
                                    match uu____6010 with
                                    | (t,uu____6016) ->
                                        encode_term t
                                          (let uu___151_6017 = env  in
                                           {
                                             bindings =
                                               (uu___151_6017.bindings);
                                             depth = (uu___151_6017.depth);
                                             tcenv = (uu___151_6017.tcenv);
                                             warn = (uu___151_6017.warn);
                                             cache = (uu___151_6017.cache);
                                             nolabels =
                                               (uu___151_6017.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___151_6017.encode_non_total_function_typ)
                                           })))
                             in
                          FStar_All.pipe_right _0_510 FStar_List.unzip  in
                        match uu____5988 with
                        | (p,decls) -> (p, (FStar_List.flatten decls))))
                 in
              FStar_All.pipe_right _0_511 FStar_List.unzip  in
            (match uu____5953 with
             | (pats,decls') ->
                 let uu____6051 = encode_formula body env  in
                 (match uu____6051 with
                  | (body,decls'') ->
                      let guards =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6070;
                             FStar_SMTEncoding_Term.rng = uu____6071;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6079 -> guards  in
                      let _0_512 = FStar_SMTEncoding_Util.mk_and_l guards  in
                      (vars, pats, _0_512, body,
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
                (fun uu____6115  ->
                   match uu____6115 with
                   | (x,uu____6119) ->
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
               let _0_514 = FStar_Syntax_Free.names hd  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let _0_513 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out _0_513) _0_514 tl
                in
             let uu____6129 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6141  ->
                       match uu____6141 with
                       | (b,uu____6145) ->
                           Prims.op_Negation (FStar_Util.set_mem b pat_vars)))
                in
             (match uu____6129 with
              | None  -> ()
              | Some (x,uu____6149) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd.FStar_Syntax_Syntax.pos tl
                     in
                  let _0_516 =
                    let _0_515 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      _0_515
                     in
                  FStar_Errors.warn pos _0_516)
          in
       let uu____6159 = FStar_Syntax_Util.destruct_typ_as_formula phi  in
       match uu____6159 with
       | None  -> fallback phi
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6165 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____6201  ->
                     match uu____6201 with
                     | (l,uu____6211) -> FStar_Ident.lid_equals op l))
              in
           (match uu____6165 with
            | None  -> fallback phi
            | Some (uu____6234,f) -> f phi.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6263 = encode_q_body env vars pats body  in
             match uu____6263 with
             | (vars,pats,guard,body,decls) ->
                 let tm =
                   let _0_518 =
                     let _0_517 = FStar_SMTEncoding_Util.mkImp (guard, body)
                        in
                     (pats, vars, _0_517)  in
                   FStar_SMTEncoding_Term.mkForall _0_518
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____6300 = encode_q_body env vars pats body  in
             match uu____6300 with
             | (vars,pats,guard,body,decls) ->
                 let _0_521 =
                   let _0_520 =
                     let _0_519 = FStar_SMTEncoding_Util.mkAnd (guard, body)
                        in
                     (pats, vars, _0_519)  in
                   FStar_SMTEncoding_Term.mkExists _0_520
                     phi.FStar_Syntax_Syntax.pos
                    in
                 (_0_521, decls))))

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
  let uu____6373 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____6373 with
  | (asym,a) ->
      let uu____6378 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____6378 with
       | (xsym,x) ->
           let uu____6383 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____6383 with
            | (ysym,y) ->
                let quant vars body x =
                  let xname_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_522 =
                         FStar_All.pipe_right vars (FStar_List.map Prims.snd)
                          in
                       (x, _0_522, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  let xtok = Prims.strcat x "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    FStar_SMTEncoding_Util.mkApp
                      (let _0_523 =
                         FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                          in
                       (x, _0_523))
                     in
                  let xtok = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok vars  in
                  let _0_533 =
                    let _0_532 =
                      let _0_531 =
                        let _0_530 =
                          FStar_SMTEncoding_Term.Assume
                            (let _0_525 =
                               FStar_SMTEncoding_Util.mkForall
                                 (let _0_524 =
                                    FStar_SMTEncoding_Util.mkEq (xapp, body)
                                     in
                                  ([[xapp]], vars, _0_524))
                                in
                             (_0_525, None,
                               (Some (Prims.strcat "primitive_" x))))
                           in
                        let _0_529 =
                          let _0_528 =
                            FStar_SMTEncoding_Term.Assume
                              (let _0_527 =
                                 FStar_SMTEncoding_Util.mkForall
                                   (let _0_526 =
                                      FStar_SMTEncoding_Util.mkEq
                                        (xtok_app, xapp)
                                       in
                                    ([[xtok_app]], vars, _0_526))
                                  in
                               (_0_527, (Some "Name-token correspondence"),
                                 (Some
                                    (Prims.strcat "token_correspondence_" x))))
                             in
                          [_0_528]  in
                        _0_530 :: _0_529  in
                      xtok_decl :: _0_531  in
                    xname_decl :: _0_532  in
                  (xtok, _0_533)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims =
                  let _0_629 =
                    let _0_536 =
                      let _0_535 =
                        let _0_534 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          _0_534
                         in
                      quant axy _0_535  in
                    (FStar_Syntax_Const.op_Eq, _0_536)  in
                  let _0_628 =
                    let _0_627 =
                      let _0_539 =
                        let _0_538 =
                          let _0_537 =
                            FStar_SMTEncoding_Util.mkNot
                              (FStar_SMTEncoding_Util.mkEq (x, y))
                             in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            _0_537
                           in
                        quant axy _0_538  in
                      (FStar_Syntax_Const.op_notEq, _0_539)  in
                    let _0_626 =
                      let _0_625 =
                        let _0_544 =
                          let _0_543 =
                            let _0_542 =
                              FStar_SMTEncoding_Util.mkLT
                                (let _0_541 =
                                   FStar_SMTEncoding_Term.unboxInt x  in
                                 let _0_540 =
                                   FStar_SMTEncoding_Term.unboxInt y  in
                                 (_0_541, _0_540))
                               in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool _0_542
                             in
                          quant xy _0_543  in
                        (FStar_Syntax_Const.op_LT, _0_544)  in
                      let _0_624 =
                        let _0_623 =
                          let _0_549 =
                            let _0_548 =
                              let _0_547 =
                                FStar_SMTEncoding_Util.mkLTE
                                  (let _0_546 =
                                     FStar_SMTEncoding_Term.unboxInt x  in
                                   let _0_545 =
                                     FStar_SMTEncoding_Term.unboxInt y  in
                                   (_0_546, _0_545))
                                 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool _0_547
                               in
                            quant xy _0_548  in
                          (FStar_Syntax_Const.op_LTE, _0_549)  in
                        let _0_622 =
                          let _0_621 =
                            let _0_554 =
                              let _0_553 =
                                let _0_552 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_551 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_550 =
                                       FStar_SMTEncoding_Term.unboxInt y  in
                                     (_0_551, _0_550))
                                   in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool _0_552
                                 in
                              quant xy _0_553  in
                            (FStar_Syntax_Const.op_GT, _0_554)  in
                          let _0_620 =
                            let _0_619 =
                              let _0_559 =
                                let _0_558 =
                                  let _0_557 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_556 =
                                         FStar_SMTEncoding_Term.unboxInt x
                                          in
                                       let _0_555 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       (_0_556, _0_555))
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool _0_557
                                   in
                                quant xy _0_558  in
                              (FStar_Syntax_Const.op_GTE, _0_559)  in
                            let _0_618 =
                              let _0_617 =
                                let _0_564 =
                                  let _0_563 =
                                    let _0_562 =
                                      FStar_SMTEncoding_Util.mkSub
                                        (let _0_561 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         let _0_560 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         (_0_561, _0_560))
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt _0_562
                                     in
                                  quant xy _0_563  in
                                (FStar_Syntax_Const.op_Subtraction, _0_564)
                                 in
                              let _0_616 =
                                let _0_615 =
                                  let _0_567 =
                                    let _0_566 =
                                      let _0_565 =
                                        FStar_SMTEncoding_Util.mkMinus
                                          (FStar_SMTEncoding_Term.unboxInt x)
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt _0_565
                                       in
                                    quant qx _0_566  in
                                  (FStar_Syntax_Const.op_Minus, _0_567)  in
                                let _0_614 =
                                  let _0_613 =
                                    let _0_572 =
                                      let _0_571 =
                                        let _0_570 =
                                          FStar_SMTEncoding_Util.mkAdd
                                            (let _0_569 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 x
                                                in
                                             let _0_568 =
                                               FStar_SMTEncoding_Term.unboxInt
                                                 y
                                                in
                                             (_0_569, _0_568))
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          _0_570
                                         in
                                      quant xy _0_571  in
                                    (FStar_Syntax_Const.op_Addition, _0_572)
                                     in
                                  let _0_612 =
                                    let _0_611 =
                                      let _0_577 =
                                        let _0_576 =
                                          let _0_575 =
                                            FStar_SMTEncoding_Util.mkMul
                                              (let _0_574 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   x
                                                  in
                                               let _0_573 =
                                                 FStar_SMTEncoding_Term.unboxInt
                                                   y
                                                  in
                                               (_0_574, _0_573))
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            _0_575
                                           in
                                        quant xy _0_576  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        _0_577)
                                       in
                                    let _0_610 =
                                      let _0_609 =
                                        let _0_582 =
                                          let _0_581 =
                                            let _0_580 =
                                              FStar_SMTEncoding_Util.mkDiv
                                                (let _0_579 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     x
                                                    in
                                                 let _0_578 =
                                                   FStar_SMTEncoding_Term.unboxInt
                                                     y
                                                    in
                                                 (_0_579, _0_578))
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              _0_580
                                             in
                                          quant xy _0_581  in
                                        (FStar_Syntax_Const.op_Division,
                                          _0_582)
                                         in
                                      let _0_608 =
                                        let _0_607 =
                                          let _0_587 =
                                            let _0_586 =
                                              let _0_585 =
                                                FStar_SMTEncoding_Util.mkMod
                                                  (let _0_584 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       x
                                                      in
                                                   let _0_583 =
                                                     FStar_SMTEncoding_Term.unboxInt
                                                       y
                                                      in
                                                   (_0_584, _0_583))
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                _0_585
                                               in
                                            quant xy _0_586  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            _0_587)
                                           in
                                        let _0_606 =
                                          let _0_605 =
                                            let _0_592 =
                                              let _0_591 =
                                                let _0_590 =
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    (let _0_589 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         x
                                                        in
                                                     let _0_588 =
                                                       FStar_SMTEncoding_Term.unboxBool
                                                         y
                                                        in
                                                     (_0_589, _0_588))
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  _0_590
                                                 in
                                              quant xy _0_591  in
                                            (FStar_Syntax_Const.op_And,
                                              _0_592)
                                             in
                                          let _0_604 =
                                            let _0_603 =
                                              let _0_597 =
                                                let _0_596 =
                                                  let _0_595 =
                                                    FStar_SMTEncoding_Util.mkOr
                                                      (let _0_594 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           x
                                                          in
                                                       let _0_593 =
                                                         FStar_SMTEncoding_Term.unboxBool
                                                           y
                                                          in
                                                       (_0_594, _0_593))
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    _0_595
                                                   in
                                                quant xy _0_596  in
                                              (FStar_Syntax_Const.op_Or,
                                                _0_597)
                                               in
                                            let _0_602 =
                                              let _0_601 =
                                                let _0_600 =
                                                  let _0_599 =
                                                    let _0_598 =
                                                      FStar_SMTEncoding_Util.mkNot
                                                        (FStar_SMTEncoding_Term.unboxBool
                                                           x)
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      _0_598
                                                     in
                                                  quant qx _0_599  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  _0_600)
                                                 in
                                              [_0_601]  in
                                            _0_603 :: _0_602  in
                                          _0_605 :: _0_604  in
                                        _0_607 :: _0_606  in
                                      _0_609 :: _0_608  in
                                    _0_611 :: _0_610  in
                                  _0_613 :: _0_612  in
                                _0_615 :: _0_614  in
                              _0_617 :: _0_616  in
                            _0_619 :: _0_618  in
                          _0_621 :: _0_620  in
                        _0_623 :: _0_622  in
                      _0_625 :: _0_624  in
                    _0_627 :: _0_626  in
                  _0_629 :: _0_628  in
                let mk l v =
                  let _0_631 =
                    let _0_630 =
                      FStar_All.pipe_right prims
                        (FStar_List.find
                           (fun uu____6729  ->
                              match uu____6729 with
                              | (l',uu____6738) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right _0_630
                      (FStar_Option.map
                         (fun uu____6759  ->
                            match uu____6759 with | (uu____6770,b) -> b v))
                     in
                  FStar_All.pipe_right _0_631 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims
                    (FStar_Util.for_some
                       (fun uu____6804  ->
                          match uu____6804 with
                          | (l',uu____6813) -> FStar_Ident.lid_equals l l'))
                   in
                { mk; is }))
  
let pretype_axiom :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.decl
  =
  fun tapp  ->
    fun vars  ->
      let uu____6836 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      match uu____6836 with
      | (xxsym,xx) ->
          let uu____6841 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
             in
          (match uu____6841 with
           | (ffsym,ff) ->
               let xx_has_type =
                 FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
               let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
               FStar_SMTEncoding_Term.Assume
                 (let _0_637 =
                    FStar_SMTEncoding_Util.mkForall
                      (let _0_634 =
                         FStar_SMTEncoding_Util.mkImp
                           (let _0_633 =
                              FStar_SMTEncoding_Util.mkEq
                                (let _0_632 =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("PreType", [xx])
                                    in
                                 (tapp, _0_632))
                               in
                            (xx_has_type, _0_633))
                          in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         _0_634))
                     in
                  let _0_636 =
                    Some
                      (varops.mk_unique
                         (let _0_635 = FStar_Util.digest_of_string tapp_hash
                             in
                          Prims.strcat "pretyping_" _0_635))
                     in
                  (_0_637, (Some "pretyping"), _0_636)))
  
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
    let _0_644 =
      FStar_SMTEncoding_Term.Assume
        (let _0_638 =
           FStar_SMTEncoding_Term.mk_HasType
             FStar_SMTEncoding_Term.mk_Term_unit tt
            in
         (_0_638, (Some "unit typing"), (Some "unit_typing")))
       in
    let _0_643 =
      let _0_642 =
        FStar_SMTEncoding_Term.Assume
          (let _0_641 =
             mkForall_fuel
               (let _0_640 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_639 =
                       FStar_SMTEncoding_Util.mkEq
                         (x, FStar_SMTEncoding_Term.mk_Term_unit)
                        in
                     (typing_pred, _0_639))
                   in
                ([[typing_pred]], [xx], _0_640))
              in
           (_0_641, (Some "unit inversion"), (Some "unit_inversion")))
         in
      [_0_642]  in
    _0_644 :: _0_643  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_656 =
      FStar_SMTEncoding_Term.Assume
        (let _0_650 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_649 =
                let _0_646 =
                  let _0_645 = FStar_SMTEncoding_Term.boxBool b  in [_0_645]
                   in
                [_0_646]  in
              let _0_648 =
                let _0_647 = FStar_SMTEncoding_Term.boxBool b  in
                FStar_SMTEncoding_Term.mk_HasType _0_647 tt  in
              (_0_649, [bb], _0_648))
            in
         (_0_650, (Some "bool typing"), (Some "bool_typing")))
       in
    let _0_655 =
      let _0_654 =
        FStar_SMTEncoding_Term.Assume
          (let _0_653 =
             mkForall_fuel
               (let _0_652 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_651 =
                       FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                     (typing_pred, _0_651))
                   in
                ([[typing_pred]], [xx], _0_652))
              in
           (_0_653, (Some "bool inversion"), (Some "bool_inversion")))
         in
      [_0_654]  in
    _0_656 :: _0_655  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let _0_663 =
        FStar_SMTEncoding_Util.mkApp
          (let _0_662 =
             let _0_661 =
               let _0_660 =
                 let _0_659 = FStar_SMTEncoding_Term.boxInt a  in
                 let _0_658 =
                   let _0_657 = FStar_SMTEncoding_Term.boxInt b  in [_0_657]
                    in
                 _0_659 :: _0_658  in
               tt :: _0_660  in
             tt :: _0_661  in
           ("Prims.Precedes", _0_662))
         in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_663  in
    let precedes_y_x =
      let _0_664 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _0_664  in
    let _0_694 =
      FStar_SMTEncoding_Term.Assume
        (let _0_670 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_669 =
                let _0_666 =
                  let _0_665 = FStar_SMTEncoding_Term.boxInt b  in [_0_665]
                   in
                [_0_666]  in
              let _0_668 =
                let _0_667 = FStar_SMTEncoding_Term.boxInt b  in
                FStar_SMTEncoding_Term.mk_HasType _0_667 tt  in
              (_0_669, [bb], _0_668))
            in
         (_0_670, (Some "int typing"), (Some "int_typing")))
       in
    let _0_693 =
      let _0_692 =
        FStar_SMTEncoding_Term.Assume
          (let _0_673 =
             mkForall_fuel
               (let _0_672 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_671 = FStar_SMTEncoding_Term.mk_tester "BoxInt" x
                        in
                     (typing_pred, _0_671))
                   in
                ([[typing_pred]], [xx], _0_672))
              in
           (_0_673, (Some "int inversion"), (Some "int_inversion")))
         in
      let _0_691 =
        let _0_690 =
          FStar_SMTEncoding_Term.Assume
            (let _0_689 =
               mkForall_fuel
                 (let _0_688 =
                    FStar_SMTEncoding_Util.mkImp
                      (let _0_687 =
                         FStar_SMTEncoding_Util.mk_and_l
                           (let _0_686 =
                              let _0_685 =
                                let _0_684 =
                                  FStar_SMTEncoding_Util.mkGT
                                    (let _0_675 =
                                       FStar_SMTEncoding_Term.unboxInt x  in
                                     let _0_674 =
                                       FStar_SMTEncoding_Util.mkInteger'
                                         (Prims.parse_int "0")
                                        in
                                     (_0_675, _0_674))
                                   in
                                let _0_683 =
                                  let _0_682 =
                                    FStar_SMTEncoding_Util.mkGTE
                                      (let _0_677 =
                                         FStar_SMTEncoding_Term.unboxInt y
                                          in
                                       let _0_676 =
                                         FStar_SMTEncoding_Util.mkInteger'
                                           (Prims.parse_int "0")
                                          in
                                       (_0_677, _0_676))
                                     in
                                  let _0_681 =
                                    let _0_680 =
                                      FStar_SMTEncoding_Util.mkLT
                                        (let _0_679 =
                                           FStar_SMTEncoding_Term.unboxInt y
                                            in
                                         let _0_678 =
                                           FStar_SMTEncoding_Term.unboxInt x
                                            in
                                         (_0_679, _0_678))
                                       in
                                    [_0_680]  in
                                  _0_682 :: _0_681  in
                                _0_684 :: _0_683  in
                              typing_pred_y :: _0_685  in
                            typing_pred :: _0_686)
                          in
                       (_0_687, precedes_y_x))
                     in
                  ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                    _0_688))
                in
             (_0_689, (Some "well-founded ordering on nat (alt)"),
               (Some "well-founded-ordering-on-nat")))
           in
        [_0_690]  in
      _0_692 :: _0_691  in
    _0_694 :: _0_693  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let _0_706 =
      FStar_SMTEncoding_Term.Assume
        (let _0_700 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_699 =
                let _0_696 =
                  let _0_695 = FStar_SMTEncoding_Term.boxString b  in
                  [_0_695]  in
                [_0_696]  in
              let _0_698 =
                let _0_697 = FStar_SMTEncoding_Term.boxString b  in
                FStar_SMTEncoding_Term.mk_HasType _0_697 tt  in
              (_0_699, [bb], _0_698))
            in
         (_0_700, (Some "string typing"), (Some "string_typing")))
       in
    let _0_705 =
      let _0_704 =
        FStar_SMTEncoding_Term.Assume
          (let _0_703 =
             mkForall_fuel
               (let _0_702 =
                  FStar_SMTEncoding_Util.mkImp
                    (let _0_701 =
                       FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                     (typing_pred, _0_701))
                   in
                ([[typing_pred]], [xx], _0_702))
              in
           (_0_703, (Some "string inversion"), (Some "string_inversion")))
         in
      [_0_704]  in
    _0_706 :: _0_705  in
  let mk_ref env reft_name uu____7061 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      FStar_SMTEncoding_Util.mkApp
        (let _0_708 =
           let _0_707 = FStar_SMTEncoding_Util.mkFreeV aa  in [_0_707]  in
         (reft_name, _0_708))
       in
    let refb =
      FStar_SMTEncoding_Util.mkApp
        (let _0_710 =
           let _0_709 = FStar_SMTEncoding_Util.mkFreeV bb  in [_0_709]  in
         (reft_name, _0_710))
       in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let _0_723 =
      FStar_SMTEncoding_Term.Assume
        (let _0_713 =
           mkForall_fuel
             (let _0_712 =
                FStar_SMTEncoding_Util.mkImp
                  (let _0_711 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                      in
                   (typing_pred, _0_711))
                 in
              ([[typing_pred]], [xx; aa], _0_712))
            in
         (_0_713, (Some "ref inversion"), (Some "ref_inversion")))
       in
    let _0_722 =
      let _0_721 =
        FStar_SMTEncoding_Term.Assume
          (let _0_720 =
             let _0_719 =
               let _0_718 =
                 FStar_SMTEncoding_Util.mkImp
                   (let _0_717 =
                      FStar_SMTEncoding_Util.mkAnd
                        (typing_pred, typing_pred_b)
                       in
                    let _0_716 =
                      FStar_SMTEncoding_Util.mkEq
                        (let _0_715 = FStar_SMTEncoding_Util.mkFreeV aa  in
                         let _0_714 = FStar_SMTEncoding_Util.mkFreeV bb  in
                         (_0_715, _0_714))
                       in
                    (_0_717, _0_716))
                  in
               ([[typing_pred; typing_pred_b]], [xx; aa; bb], _0_718)  in
             mkForall_fuel' (Prims.parse_int "2") _0_719  in
           (_0_720, (Some "ref typing is injective"),
             (Some "ref_injectivity")))
         in
      [_0_721]  in
    _0_723 :: _0_722  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Term.Assume
       (valid, (Some "True interpretation"), (Some "true_interp"))]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let _0_725 =
      FStar_SMTEncoding_Term.Assume
        (let _0_724 =
           FStar_SMTEncoding_Util.mkIff
             (FStar_SMTEncoding_Util.mkFalse, valid)
            in
         (_0_724, (Some "False interpretation"), (Some "false_interp")))
       in
    [_0_725]  in
  let mk_and_interp env conj uu____7146 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_727 =
           let _0_726 = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
           [_0_726]  in
         ("Valid", _0_727))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_731 =
      FStar_SMTEncoding_Term.Assume
        (let _0_730 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_729 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_728 =
                     FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                   (_0_728, valid))
                 in
              ([[valid]], [aa; bb], _0_729))
            in
         (_0_730, (Some "/\\ interpretation"), (Some "l_and-interp")))
       in
    [_0_731]  in
  let mk_or_interp env disj uu____7186 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_733 =
           let _0_732 = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
           [_0_732]  in
         ("Valid", _0_733))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_737 =
      FStar_SMTEncoding_Term.Assume
        (let _0_736 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_735 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_734 =
                     FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                   (_0_734, valid))
                 in
              ([[valid]], [aa; bb], _0_735))
            in
         (_0_736, (Some "\\/ interpretation"), (Some "l_or-interp")))
       in
    [_0_737]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let y = FStar_SMTEncoding_Util.mkFreeV yy  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_739 =
           let _0_738 = FStar_SMTEncoding_Util.mkApp (eq2, [a; x; y])  in
           [_0_738]  in
         ("Valid", _0_739))
       in
    let _0_743 =
      FStar_SMTEncoding_Term.Assume
        (let _0_742 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_741 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_740 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_740, valid))
                 in
              ([[valid]], [aa; xx; yy], _0_741))
            in
         (_0_742, (Some "Eq2 interpretation"), (Some "eq2-interp")))
       in
    [_0_743]  in
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
        (let _0_745 =
           let _0_744 = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x; y])  in
           [_0_744]  in
         ("Valid", _0_745))
       in
    let _0_749 =
      FStar_SMTEncoding_Term.Assume
        (let _0_748 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_747 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_746 = FStar_SMTEncoding_Util.mkEq (x, y)  in
                   (_0_746, valid))
                 in
              ([[valid]], [aa; bb; xx; yy], _0_747))
            in
         (_0_748, (Some "Eq3 interpretation"), (Some "eq3-interp")))
       in
    [_0_749]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_751 =
           let _0_750 = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
           [_0_750]  in
         ("Valid", _0_751))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_755 =
      FStar_SMTEncoding_Term.Assume
        (let _0_754 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_753 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_752 =
                     FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                   (_0_752, valid))
                 in
              ([[valid]], [aa; bb], _0_753))
            in
         (_0_754, (Some "==> interpretation"), (Some "l_imp-interp")))
       in
    [_0_755]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_757 =
           let _0_756 = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
           [_0_756]  in
         ("Valid", _0_757))
       in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let _0_761 =
      FStar_SMTEncoding_Term.Assume
        (let _0_760 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_759 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_758 =
                     FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                   (_0_758, valid))
                 in
              ([[valid]], [aa; bb], _0_759))
            in
         (_0_760, (Some "<==> interpretation"), (Some "l_iff-interp")))
       in
    [_0_761]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_763 =
           let _0_762 = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
           [_0_762]  in
         ("Valid", _0_763))
       in
    let not_valid_a =
      let _0_764 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _0_764  in
    let _0_767 =
      FStar_SMTEncoding_Term.Assume
        (let _0_766 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_765 = FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)
                 in
              ([[valid]], [aa], _0_765))
            in
         (_0_766, (Some "not interpretation"), (Some "l_not-interp")))
       in
    [_0_767]  in
  let mk_forall_interp env for_all tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_769 =
           let _0_768 = FStar_SMTEncoding_Util.mkApp (for_all, [a; b])  in
           [_0_768]  in
         ("Valid", _0_769))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_771 =
           let _0_770 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_770]
            in
         ("Valid", _0_771))
       in
    let _0_780 =
      FStar_SMTEncoding_Term.Assume
        (let _0_779 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_778 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_777 =
                     FStar_SMTEncoding_Util.mkForall
                       (let _0_776 =
                          let _0_773 =
                            let _0_772 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_772]  in
                          [_0_773]  in
                        let _0_775 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_774 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_774, valid_b_x))
                           in
                        (_0_776, [xx], _0_775))
                      in
                   (_0_777, valid))
                 in
              ([[valid]], [aa; bb], _0_778))
            in
         (_0_779, (Some "forall interpretation"), (Some "forall-interp")))
       in
    [_0_780]  in
  let mk_exists_interp env for_some tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x = FStar_SMTEncoding_Util.mkFreeV xx  in
    let valid =
      FStar_SMTEncoding_Util.mkApp
        (let _0_782 =
           let _0_781 = FStar_SMTEncoding_Util.mkApp (for_some, [a; b])  in
           [_0_781]  in
         ("Valid", _0_782))
       in
    let valid_b_x =
      FStar_SMTEncoding_Util.mkApp
        (let _0_784 =
           let _0_783 = FStar_SMTEncoding_Util.mk_ApplyTT b x  in [_0_783]
            in
         ("Valid", _0_784))
       in
    let _0_793 =
      FStar_SMTEncoding_Term.Assume
        (let _0_792 =
           FStar_SMTEncoding_Util.mkForall
             (let _0_791 =
                FStar_SMTEncoding_Util.mkIff
                  (let _0_790 =
                     FStar_SMTEncoding_Util.mkExists
                       (let _0_789 =
                          let _0_786 =
                            let _0_785 =
                              FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                            [_0_785]  in
                          [_0_786]  in
                        let _0_788 =
                          FStar_SMTEncoding_Util.mkImp
                            (let _0_787 =
                               FStar_SMTEncoding_Term.mk_HasTypeZ x a  in
                             (_0_787, valid_b_x))
                           in
                        (_0_789, [xx], _0_788))
                      in
                   (_0_790, valid))
                 in
              ([[valid]], [aa; bb], _0_791))
            in
         (_0_792, (Some "exists interpretation"), (Some "exists-interp")))
       in
    [_0_793]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let _0_796 =
      FStar_SMTEncoding_Term.Assume
        (let _0_795 =
           FStar_SMTEncoding_Term.mk_HasTypeZ
             FStar_SMTEncoding_Term.mk_Range_const range_ty
            in
         let _0_794 = Some (varops.mk_unique "typing_range_const")  in
         (_0_795, (Some "Range_const typing"), _0_794))
       in
    [_0_796]  in
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
          let uu____7799 =
            FStar_Util.find_opt
              (fun uu____7817  ->
                 match uu____7817 with
                 | (l,uu____7827) -> FStar_Ident.lid_equals l t) prims
             in
          match uu____7799 with
          | None  -> []
          | Some (uu____7849,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____7886 = encode_function_type_as_formula None None t env  in
        match uu____7886 with
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
            let uu____7919 =
              (let _0_797 =
                 FStar_Syntax_Util.is_pure_or_ghost_function t_norm  in
               FStar_All.pipe_left Prims.op_Negation _0_797) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____7919
            then
              let uu____7923 = new_term_constant_and_tok_from_lid env lid  in
              match uu____7923 with
              | (vname,vtok,env) ->
                  let arg_sorts =
                    let uu____7935 =
                      (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                       in
                    match uu____7935 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____7938) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____7955  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____7958 -> []  in
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
              (let uu____7967 = prims.is lid  in
               if uu____7967
               then
                 let vname = varops.new_fvar lid  in
                 let uu____7972 = prims.mk lid vname  in
                 match uu____7972 with
                 | (tok,definition) ->
                     let env = push_free_var env lid vname (Some tok)  in
                     (definition, env)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____7987 =
                    let uu____7993 = curried_arrow_formals_comp t_norm  in
                    match uu____7993 with
                    | (args,comp) ->
                        if encode_non_total_function_typ
                        then
                          let _0_798 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp
                             in
                          (args, _0_798)
                        else
                          (let _0_800 =
                             let _0_799 =
                               FStar_TypeChecker_Env.result_typ env.tcenv
                                 comp
                                in
                             (None, _0_799)  in
                           (args, _0_800))
                     in
                  match uu____7987 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____8027 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____8027 with
                       | (vname,vtok,env) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____8040 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___124_8064  ->
                                     match uu___124_8064 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____8067 =
                                           FStar_Util.prefix vars  in
                                         (match uu____8067 with
                                          | (uu____8078,(xxsym,uu____8080))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let _0_805 =
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_804 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_803 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (let _0_802 =
                                                               let _0_801 =
                                                                 FStar_SMTEncoding_Term.mk_tester
                                                                   (escape
                                                                    d.FStar_Ident.str)
                                                                   xx
                                                                  in
                                                               FStar_All.pipe_left
                                                                 FStar_SMTEncoding_Term.boxBool
                                                                 _0_801
                                                                in
                                                             (vapp, _0_802))
                                                           in
                                                        ([[vapp]], vars,
                                                          _0_803))
                                                      in
                                                   (_0_804,
                                                     (Some
                                                        "Discriminator equation"),
                                                     (Some
                                                        (Prims.strcat
                                                           "disc_equation_"
                                                           (escape
                                                              d.FStar_Ident.str)))))
                                                 in
                                              [_0_805])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____8101 =
                                           FStar_Util.prefix vars  in
                                         (match uu____8101 with
                                          | (uu____8112,(xxsym,uu____8114))
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
                                              let _0_808 =
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_807 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_806 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          _0_806))
                                                      in
                                                   (_0_807,
                                                     (Some
                                                        "Projector equation"),
                                                     (Some
                                                        (Prims.strcat
                                                           "proj_equation_"
                                                           tp_name))))
                                                 in
                                              [_0_808])
                                     | uu____8137 -> []))
                              in
                           let uu____8138 = encode_binders None formals env
                              in
                           (match uu____8138 with
                            | (vars,guards,env',decls1,uu____8154) ->
                                let uu____8161 =
                                  match pre_opt with
                                  | None  ->
                                      let _0_809 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (_0_809, decls1)
                                  | Some p ->
                                      let uu____8167 = encode_formula p env'
                                         in
                                      (match uu____8167 with
                                       | (g,ds) ->
                                           let _0_810 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (_0_810,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____8161 with
                                 | (guard,decls1) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       FStar_SMTEncoding_Util.mkApp
                                         (let _0_811 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars
                                             in
                                          (vname, _0_811))
                                        in
                                     let uu____8185 =
                                       let vname_decl =
                                         FStar_SMTEncoding_Term.DeclFun
                                           (let _0_812 =
                                              FStar_All.pipe_right formals
                                                (FStar_List.map
                                                   (fun uu____8195  ->
                                                      FStar_SMTEncoding_Term.Term_sort))
                                               in
                                            (vname, _0_812,
                                              FStar_SMTEncoding_Term.Term_sort,
                                              None))
                                          in
                                       let uu____8198 =
                                         let env =
                                           let uu___152_8202 = env  in
                                           {
                                             bindings =
                                               (uu___152_8202.bindings);
                                             depth = (uu___152_8202.depth);
                                             tcenv = (uu___152_8202.tcenv);
                                             warn = (uu___152_8202.warn);
                                             cache = (uu___152_8202.cache);
                                             nolabels =
                                               (uu___152_8202.nolabels);
                                             use_zfuel_name =
                                               (uu___152_8202.use_zfuel_name);
                                             encode_non_total_function_typ
                                           }  in
                                         let uu____8203 =
                                           Prims.op_Negation
                                             (head_normal env tt)
                                            in
                                         if uu____8203
                                         then
                                           encode_term_pred None tt env
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env
                                             vtok_tm
                                          in
                                       match uu____8198 with
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
                                           let uu____8215 =
                                             match formals with
                                             | [] ->
                                                 let _0_816 =
                                                   let _0_815 =
                                                     let _0_814 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_813  ->
                                                          Some _0_813) _0_814
                                                      in
                                                   push_free_var env lid
                                                     vname _0_815
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing]), _0_816)
                                             | uu____8226 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let _0_817 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     _0_817
                                                    in
                                                 let name_tok_corr =
                                                   FStar_SMTEncoding_Term.Assume
                                                     (let _0_819 =
                                                        FStar_SMTEncoding_Util.mkForall
                                                          (let _0_818 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             _0_818))
                                                         in
                                                      (_0_819,
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
                                           (match uu____8215 with
                                            | (tok_decl,env) ->
                                                ((vname_decl :: tok_decl),
                                                  env))
                                        in
                                     (match uu____8185 with
                                      | (decls2,env) ->
                                          let uu____8256 =
                                            let res_t =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____8261 =
                                              encode_term res_t env'  in
                                            match uu____8261 with
                                            | (encoded_res_t,decls) ->
                                                let _0_820 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, _0_820,
                                                  decls)
                                             in
                                          (match uu____8256 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 FStar_SMTEncoding_Term.Assume
                                                   (let _0_822 =
                                                      FStar_SMTEncoding_Util.mkForall
                                                        (let _0_821 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           _0_821))
                                                       in
                                                    (_0_822,
                                                      (Some "free var typing"),
                                                      (Some
                                                         (Prims.strcat
                                                            "typing_" vname))))
                                                  in
                                               let freshness =
                                                 let uu____8285 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____8285
                                                 then
                                                   let _0_827 =
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       (let _0_824 =
                                                          FStar_All.pipe_right
                                                            vars
                                                            (FStar_List.map
                                                               Prims.snd)
                                                           in
                                                        let _0_823 =
                                                          varops.next_id ()
                                                           in
                                                        (vname, _0_824,
                                                          FStar_SMTEncoding_Term.Term_sort,
                                                          _0_823))
                                                      in
                                                   let _0_826 =
                                                     let _0_825 =
                                                       pretype_axiom vapp
                                                         vars
                                                        in
                                                     [_0_825]  in
                                                   _0_827 :: _0_826
                                                 else []  in
                                               let g =
                                                 let _0_832 =
                                                   let _0_831 =
                                                     let _0_830 =
                                                       let _0_829 =
                                                         let _0_828 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx :: _0_828
                                                          in
                                                       FStar_List.append
                                                         freshness _0_829
                                                        in
                                                     FStar_List.append decls3
                                                       _0_830
                                                      in
                                                   FStar_List.append decls2
                                                     _0_831
                                                    in
                                                 FStar_List.append decls1
                                                   _0_832
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
          let uu____8316 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____8316 with
          | None  ->
              let uu____8339 = encode_free_var env x t t_norm []  in
              (match uu____8339 with
               | (decls,env) ->
                   let uu____8354 =
                     lookup_lid env
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____8354 with
                    | (n,x',uu____8373) -> ((n, x'), decls, env)))
          | Some (n,x,uu____8385) -> ((n, x), [], env)
  
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
          let uu____8418 = encode_free_var env lid t tt quals  in
          match uu____8418 with
          | (decls,env) ->
              let uu____8429 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____8429
              then
                let _0_834 =
                  let _0_833 = encode_smt_lemma env lid tt  in
                  FStar_List.append decls _0_833  in
                (_0_834, env)
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
             (fun uu____8459  ->
                fun lb  ->
                  match uu____8459 with
                  | (decls,env) ->
                      let uu____8471 =
                        let _0_835 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env _0_835
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____8471 with
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
    fun uu____8498  ->
      fun quals  ->
        match uu____8498 with
        | (is_rec,bindings) ->
            let eta_expand binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____8547 = FStar_Util.first_N nbinders formals  in
              match uu____8547 with
              | (formals,extra_formals) ->
                  let subst =
                    FStar_List.map2
                      (fun uu____8587  ->
                         fun uu____8588  ->
                           match (uu____8587, uu____8588) with
                           | ((formal,uu____8598),(binder,uu____8600)) ->
                               FStar_Syntax_Syntax.NT
                                 (let _0_836 =
                                    FStar_Syntax_Syntax.bv_to_name binder  in
                                  (formal, _0_836))) formals binders
                     in
                  let extra_formals =
                    let _0_839 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____8625  ->
                              match uu____8625 with
                              | (x,i) ->
                                  let _0_838 =
                                    let uu___153_8632 = x  in
                                    let _0_837 =
                                      FStar_Syntax_Subst.subst subst
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___153_8632.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___153_8632.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = _0_837
                                    }  in
                                  (_0_838, i)))
                       in
                    FStar_All.pipe_right _0_839
                      FStar_Syntax_Util.name_binders
                     in
                  let body =
                    let _0_845 =
                      let _0_844 =
                        (FStar_Syntax_Subst.subst subst t).FStar_Syntax_Syntax.n
                         in
                      FStar_All.pipe_left (fun _0_843  -> Some _0_843) _0_844
                       in
                    (let _0_842 = FStar_Syntax_Subst.compress body  in
                     let _0_841 =
                       let _0_840 =
                         FStar_Syntax_Util.args_of_binders extra_formals  in
                       FStar_All.pipe_left Prims.snd _0_840  in
                     FStar_Syntax_Syntax.extend_app_n _0_842 _0_841) _0_845
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals), body)
               in
            let destruct_bound_function flid t_norm e =
              let rec aux norm t_norm =
                let uu____8691 = FStar_Syntax_Util.abs_formals e  in
                match uu____8691 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____8740::uu____8741 ->
                         let uu____8749 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____8749 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____8774 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____8774 with
                               | (formals,c) ->
                                   let nformals = FStar_List.length formals
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres =
                                     FStar_TypeChecker_Env.result_typ
                                       env.tcenv c
                                      in
                                   let uu____8800 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c)
                                      in
                                   if uu____8800
                                   then
                                     let uu____8818 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____8818 with
                                      | (bs0,rest) ->
                                          let c =
                                            let subst =
                                              FStar_List.map2
                                                (fun uu____8864  ->
                                                   fun uu____8865  ->
                                                     match (uu____8864,
                                                             uu____8865)
                                                     with
                                                     | ((b,uu____8875),
                                                        (x,uu____8877)) ->
                                                         FStar_Syntax_Syntax.NT
                                                           (let _0_846 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            (b, _0_846))) bs0
                                                formals
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst c
                                             in
                                          let body =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let _0_848 =
                                            let _0_847 =
                                              FStar_TypeChecker_Env.result_typ
                                                env.tcenv c
                                               in
                                            (bs0, body, bs0, _0_847)  in
                                          (_0_848, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____8917 =
                                          eta_expand binders formals body
                                            tres
                                           in
                                        match uu____8917 with
                                        | (binders,body) ->
                                            ((binders, body, formals, tres),
                                              false))
                                     else
                                       ((binders, body, formals, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____8969) ->
                              let _0_849 =
                                Prims.fst
                                  (aux norm x.FStar_Syntax_Syntax.sort)
                                 in
                              (_0_849, true)
                          | uu____8994 when Prims.op_Negation norm ->
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
                          | uu____8996 ->
                              failwith
                                (let _0_851 =
                                   FStar_Syntax_Print.term_to_string e  in
                                 let _0_850 =
                                   FStar_Syntax_Print.term_to_string t_norm
                                    in
                                 FStar_Util.format3
                                   "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                   flid.FStar_Ident.str _0_851 _0_850))
                     | uu____9009 ->
                         let uu____9010 =
                           (FStar_Syntax_Subst.compress t_norm).FStar_Syntax_Syntax.n
                            in
                         (match uu____9010 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____9035 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____9035 with
                               | (formals,c) ->
                                   let tres =
                                     FStar_TypeChecker_Env.result_typ
                                       env.tcenv c
                                      in
                                   let uu____9053 =
                                     eta_expand [] formals e tres  in
                                   (match uu____9053 with
                                    | (binders,body) ->
                                        ((binders, body, formals, tres),
                                          false)))
                          | uu____9101 -> (([], e, [], t_norm), false)))
                 in
              aux false t_norm  in
            (try
               let uu____9129 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         FStar_Syntax_Util.is_lemma
                           lb.FStar_Syntax_Syntax.lbtyp))
                  in
               if uu____9129
               then encode_top_level_vals env bindings quals
               else
                 (let uu____9136 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____9177  ->
                            fun lb  ->
                              match uu____9177 with
                              | (toks,typs,decls,env) ->
                                  ((let uu____9228 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____9228
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____9231 =
                                      let _0_852 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env _0_852
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____9231 with
                                    | (tok,decl,env) ->
                                        let _0_855 =
                                          let _0_854 =
                                            let _0_853 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (_0_853, tok)  in
                                          _0_854 :: toks  in
                                        (_0_855, (t_norm :: typs), (decl ::
                                          decls), env)))) ([], [], [], env))
                     in
                  match uu____9136 with
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
                        | uu____9364 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok -> mk_Apply ftok vars
                               | None  ->
                                   let _0_856 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply _0_856 vars)
                            else
                              FStar_SMTEncoding_Util.mkApp
                                (let _0_857 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, _0_857))
                         in
                      let uu____9373 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___125_9375  ->
                                 match uu___125_9375 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____9376 -> false)))
                          ||
                          (FStar_All.pipe_right typs
                             (FStar_Util.for_some
                                (fun t  ->
                                   let _0_858 =
                                     FStar_Syntax_Util.is_pure_or_ghost_function
                                       t
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     _0_858)))
                         in
                      if uu____9373
                      then (decls, env)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs, toks) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____9398;
                                FStar_Syntax_Syntax.lbunivs = uu____9399;
                                FStar_Syntax_Syntax.lbtyp = uu____9400;
                                FStar_Syntax_Syntax.lbeff = uu____9401;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let e = FStar_Syntax_Subst.compress e  in
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____9443 =
                                 destruct_bound_function flid t_norm e  in
                               (match uu____9443 with
                                | ((binders,body,uu____9455,uu____9456),curry)
                                    ->
                                    let uu____9462 =
                                      encode_binders None binders env  in
                                    (match uu____9462 with
                                     | (vars,guards,env',binder_decls,uu____9478)
                                         ->
                                         let app = mk_app curry f ftok vars
                                            in
                                         let uu____9486 =
                                           let uu____9491 =
                                             FStar_All.pipe_right quals
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Logic)
                                              in
                                           if uu____9491
                                           then
                                             let _0_860 =
                                               FStar_SMTEncoding_Term.mk_Valid
                                                 app
                                                in
                                             let _0_859 =
                                               encode_formula body env'  in
                                             (_0_860, _0_859)
                                           else
                                             (let _0_861 =
                                                encode_term body env'  in
                                              (app, _0_861))
                                            in
                                         (match uu____9486 with
                                          | (app,(body,decls2)) ->
                                              let eqn =
                                                FStar_SMTEncoding_Term.Assume
                                                  (let _0_864 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       (let _0_862 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body)
                                                           in
                                                        ([[app]], vars,
                                                          _0_862))
                                                      in
                                                   let _0_863 =
                                                     Some
                                                       (FStar_Util.format1
                                                          "Equation for %s"
                                                          flid.FStar_Ident.str)
                                                      in
                                                   (_0_864, _0_863,
                                                     (Some
                                                        (Prims.strcat
                                                           "equation_" f))))
                                                 in
                                              let _0_869 =
                                                let _0_868 =
                                                  let _0_867 =
                                                    let _0_866 =
                                                      let _0_865 =
                                                        primitive_type_axioms
                                                          env.tcenv flid f
                                                          app
                                                         in
                                                      FStar_List.append 
                                                        [eqn] _0_865
                                                       in
                                                    FStar_List.append decls2
                                                      _0_866
                                                     in
                                                  FStar_List.append
                                                    binder_decls _0_867
                                                   in
                                                FStar_List.append decls
                                                  _0_868
                                                 in
                                              (_0_869, env))))
                           | uu____9519 -> failwith "Impossible")
                        else
                          (let fuel =
                             let _0_870 = varops.fresh "fuel"  in
                             (_0_870, FStar_SMTEncoding_Term.Fuel_sort)  in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env  in
                           let uu____9540 =
                             FStar_All.pipe_right toks
                               (FStar_List.fold_left
                                  (fun uu____9579  ->
                                     fun uu____9580  ->
                                       match (uu____9579, uu____9580) with
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
                                             let _0_873 =
                                               let _0_872 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_871  -> Some _0_871)
                                                 _0_872
                                                in
                                             push_free_var env flid gtok
                                               _0_873
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env)) ([], env))
                              in
                           match uu____9540 with
                           | (gtoks,env) ->
                               let gtoks = FStar_List.rev gtoks  in
                               let encode_one_binding env0 uu____9747 t_norm
                                 uu____9749 =
                                 match (uu____9747, uu____9749) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uu____9773;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____9774;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____9775;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     ((let uu____9793 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug
                                              env0.tcenv)
                                           (FStar_Options.Other "SMTEncoding")
                                          in
                                       if uu____9793
                                       then
                                         let _0_876 =
                                           FStar_Syntax_Print.lbname_to_string
                                             lbn
                                            in
                                         let _0_875 =
                                           FStar_Syntax_Print.term_to_string
                                             t_norm
                                            in
                                         let _0_874 =
                                           FStar_Syntax_Print.term_to_string
                                             e
                                            in
                                         FStar_Util.print3
                                           "Encoding let rec %s : %s = %s\n"
                                           _0_876 _0_875 _0_874
                                       else ());
                                      (let uu____9795 =
                                         destruct_bound_function flid t_norm
                                           e
                                          in
                                       match uu____9795 with
                                       | ((binders,body,formals,tres),curry)
                                           ->
                                           ((let uu____9817 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env0.tcenv)
                                                 (FStar_Options.Other
                                                    "SMTEncoding")
                                                in
                                             if uu____9817
                                             then
                                               let _0_878 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   ", " binders
                                                  in
                                               let _0_877 =
                                                 FStar_Syntax_Print.term_to_string
                                                   body
                                                  in
                                               FStar_Util.print2
                                                 "Encoding let rec: binders=[%s], body=%s\n"
                                                 _0_878 _0_877
                                             else ());
                                            if curry
                                            then
                                              failwith
                                                "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                            else ();
                                            (let uu____9821 =
                                               encode_binders None binders
                                                 env
                                                in
                                             match uu____9821 with
                                             | (vars,guards,env',binder_decls,uu____9839)
                                                 ->
                                                 let decl_g =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (let _0_880 =
                                                        let _0_879 =
                                                          FStar_List.map
                                                            Prims.snd vars
                                                           in
                                                        FStar_SMTEncoding_Term.Fuel_sort
                                                          :: _0_879
                                                         in
                                                      (g, _0_880,
                                                        FStar_SMTEncoding_Term.Term_sort,
                                                        (Some
                                                           "Fuel-instrumented function name")))
                                                    in
                                                 let env0 =
                                                   push_zfuel_name env0 flid
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
                                                   FStar_SMTEncoding_Util.mkApp
                                                     (let _0_881 =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars
                                                         in
                                                      (f, _0_881))
                                                    in
                                                 let gsapp =
                                                   FStar_SMTEncoding_Util.mkApp
                                                     (let _0_883 =
                                                        let _0_882 =
                                                          FStar_SMTEncoding_Util.mkApp
                                                            ("SFuel",
                                                              [fuel_tm])
                                                           in
                                                        _0_882 :: vars_tm  in
                                                      (g, _0_883))
                                                    in
                                                 let gmax =
                                                   FStar_SMTEncoding_Util.mkApp
                                                     (let _0_885 =
                                                        let _0_884 =
                                                          FStar_SMTEncoding_Util.mkApp
                                                            ("MaxFuel", [])
                                                           in
                                                        _0_884 :: vars_tm  in
                                                      (g, _0_885))
                                                    in
                                                 let uu____9869 =
                                                   encode_term body env'  in
                                                 (match uu____9869 with
                                                  | (body_tm,decls2) ->
                                                      let eqn_g =
                                                        FStar_SMTEncoding_Term.Assume
                                                          (let _0_888 =
                                                             FStar_SMTEncoding_Util.mkForall'
                                                               (let _0_886 =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  _0_886))
                                                              in
                                                           let _0_887 =
                                                             Some
                                                               (FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str)
                                                              in
                                                           (_0_888, _0_887,
                                                             (Some
                                                                (Prims.strcat
                                                                   "equation_with_fuel_"
                                                                   g))))
                                                         in
                                                      let eqn_f =
                                                        FStar_SMTEncoding_Term.Assume
                                                          (let _0_890 =
                                                             FStar_SMTEncoding_Util.mkForall
                                                               (let _0_889 =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  _0_889))
                                                              in
                                                           (_0_890,
                                                             (Some
                                                                "Correspondence of recursive function to instrumented version"),
                                                             (Some
                                                                (Prims.strcat
                                                                   "fuel_correspondence_"
                                                                   g))))
                                                         in
                                                      let eqn_g' =
                                                        FStar_SMTEncoding_Term.Assume
                                                          (let _0_895 =
                                                             FStar_SMTEncoding_Util.mkForall
                                                               (let _0_894 =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (
                                                                    let _0_893
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (let _0_892
                                                                    =
                                                                    let _0_891
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    _0_891 ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    _0_892))
                                                                     in
                                                                    (gsapp,
                                                                    _0_893))
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  _0_894))
                                                              in
                                                           (_0_895,
                                                             (Some
                                                                "Fuel irrelevance"),
                                                             (Some
                                                                (Prims.strcat
                                                                   "fuel_irrelevance_"
                                                                   g))))
                                                         in
                                                      let uu____9913 =
                                                        let uu____9918 =
                                                          encode_binders None
                                                            formals env0
                                                           in
                                                        match uu____9918 with
                                                        | (vars,v_guards,env,binder_decls,uu____9935)
                                                            ->
                                                            let vars_tm =
                                                              FStar_List.map
                                                                FStar_SMTEncoding_Util.mkFreeV
                                                                vars
                                                               in
                                                            let gapp =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                (g, (fuel_tm
                                                                  ::
                                                                  vars_tm))
                                                               in
                                                            let tok_corr =
                                                              let tok_app =
                                                                let _0_896 =
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                   in
                                                                mk_Apply
                                                                  _0_896
                                                                  (fuel ::
                                                                  vars)
                                                                 in
                                                              FStar_SMTEncoding_Term.Assume
                                                                (let _0_898 =
                                                                   FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_897))
                                                                    in
                                                                 (_0_898,
                                                                   (Some
                                                                    "Fuel token correspondence"),
                                                                   (Some
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))))
                                                               in
                                                            let uu____9963 =
                                                              let uu____9967
                                                                =
                                                                encode_term_pred
                                                                  None tres
                                                                  env gapp
                                                                 in
                                                              match uu____9967
                                                              with
                                                              | (g_typing,d3)
                                                                  ->
                                                                  let _0_903
                                                                    =
                                                                    let _0_902
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_901
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_899
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (_0_899,
                                                                    g_typing))
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    _0_900))
                                                                     in
                                                                    (_0_901,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))))  in
                                                                    [_0_902]
                                                                     in
                                                                  (d3,
                                                                    _0_903)
                                                               in
                                                            (match uu____9963
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
                                                      (match uu____9913 with
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
                                                             env0)))))))
                                  in
                               let uu____10010 =
                                 let _0_904 =
                                   FStar_List.zip3 gtoks typs bindings  in
                                 FStar_List.fold_left
                                   (fun uu____10032  ->
                                      fun uu____10033  ->
                                        match (uu____10032, uu____10033) with
                                        | ((decls,eqns,env0),(gtok,ty,lb)) ->
                                            let uu____10109 =
                                              encode_one_binding env0 gtok ty
                                                lb
                                               in
                                            (match uu____10109 with
                                             | (decls',eqns',env0) ->
                                                 ((decls' :: decls),
                                                   (FStar_List.append eqns'
                                                      eqns), env0)))
                                   ([decls], [], env0) _0_904
                                  in
                               (match uu____10010 with
                                | (decls,eqns,env0) ->
                                    let uu____10155 =
                                      let _0_905 =
                                        FStar_All.pipe_right decls
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right _0_905
                                        (FStar_List.partition
                                           (fun uu___126_10168  ->
                                              match uu___126_10168 with
                                              | FStar_SMTEncoding_Term.DeclFun
                                                  uu____10169 -> true
                                              | uu____10175 -> false))
                                       in
                                    (match uu____10155 with
                                     | (prefix_decls,rest) ->
                                         let eqns = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns)),
                                           env0)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let _0_906 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right _0_906 (FStar_String.concat " and ")
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
      (let uu____10224 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____10224
       then
         let _0_907 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _0_907
       else ());
      (let nm =
         let uu____10227 = FStar_Syntax_Util.lid_of_sigelt se  in
         match uu____10227 with | None  -> "" | Some l -> l.FStar_Ident.str
          in
       let uu____10230 = encode_sigelt' env se  in
       match uu____10230 with
       | (g,e) ->
           (match g with
            | [] ->
                let _0_909 =
                  let _0_908 =
                    FStar_SMTEncoding_Term.Caption
                      (FStar_Util.format1 "<Skipped %s/>" nm)
                     in
                  [_0_908]  in
                (_0_909, e)
            | uu____10240 ->
                let _0_914 =
                  let _0_913 =
                    let _0_910 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "<Start encoding %s>" nm)
                       in
                    _0_910 :: g  in
                  let _0_912 =
                    let _0_911 =
                      FStar_SMTEncoding_Term.Caption
                        (FStar_Util.format1 "</end encoding %s>" nm)
                       in
                    [_0_911]  in
                  FStar_List.append _0_913 _0_912  in
                (_0_914, e)))

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____10248 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____10259) ->
          let uu____10260 =
            let _0_915 =
              FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right _0_915 Prims.op_Negation  in
          if uu____10260
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____10280 ->
                   (FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_abs
                         (let _0_917 =
                            FStar_All.pipe_left (fun _0_916  -> Some _0_916)
                              (FStar_Util.Inr
                                 (FStar_Syntax_Const.effect_Tot_lid,
                                   [FStar_Syntax_Syntax.TOTAL]))
                             in
                          ((ed.FStar_Syntax_Syntax.binders), tm, _0_917))))
                     None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env a =
               let uu____10327 =
                 new_term_constant_and_tok_from_lid env
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____10327 with
               | (aname,atok,env) ->
                   let uu____10337 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____10337 with
                    | (formals,uu____10347) ->
                        let uu____10354 =
                          let _0_918 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term _0_918 env  in
                        (match uu____10354 with
                         | (tm,decls) ->
                             let a_decls =
                               let _0_920 =
                                 FStar_SMTEncoding_Term.DeclFun
                                   (let _0_919 =
                                      FStar_All.pipe_right formals
                                        (FStar_List.map
                                           (fun uu____10372  ->
                                              FStar_SMTEncoding_Term.Term_sort))
                                       in
                                    (aname, _0_919,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      (Some "Action")))
                                  in
                               [_0_920;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____10377 =
                               let _0_921 =
                                 FStar_All.pipe_right formals
                                   (FStar_List.map
                                      (fun uu____10409  ->
                                         match uu____10409 with
                                         | (bv,uu____10417) ->
                                             let uu____10418 =
                                               gen_term_var env bv  in
                                             (match uu____10418 with
                                              | (xxsym,xx,uu____10428) ->
                                                  ((xxsym,
                                                     FStar_SMTEncoding_Term.Term_sort),
                                                    xx))))
                                  in
                               FStar_All.pipe_right _0_921 FStar_List.split
                                in
                             (match uu____10377 with
                              | (xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp
                                      (let _0_923 =
                                         let _0_922 =
                                           FStar_SMTEncoding_Util.mkApp
                                             (aname, xs)
                                            in
                                         [_0_922]  in
                                       ("Reify", _0_923))
                                     in
                                  let a_eq =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_926 =
                                         FStar_SMTEncoding_Util.mkForall
                                           (let _0_925 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (let _0_924 =
                                                   mk_Apply tm xs_sorts  in
                                                 (app, _0_924))
                                               in
                                            ([[app]], xs_sorts, _0_925))
                                          in
                                       (_0_926, (Some "Action equality"),
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
                                      (let _0_928 =
                                         FStar_SMTEncoding_Util.mkForall
                                           (let _0_927 =
                                              FStar_SMTEncoding_Util.mkEq
                                                (tok_app, app)
                                               in
                                            ([[tok_app]], xs_sorts, _0_927))
                                          in
                                       (_0_928,
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
             let uu____10472 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____10472 with
             | (env,decls2) -> ((FStar_List.flatten decls2), env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10488,uu____10489,uu____10490,uu____10491) when
          FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____10494 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____10494 with | (tname,ttok,env) -> ([], env))
      | FStar_Syntax_Syntax.Sig_declare_typ
          (lid,uu____10505,t,quals,uu____10508) ->
          let will_encode_definition =
            Prims.op_Negation
              (FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___127_10513  ->
                       match uu___127_10513 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _
                           |FStar_Syntax_Syntax.Irreducible  -> true
                       | uu____10516 -> false)))
             in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____10522 = encode_top_level_val env fv t quals  in
             match uu____10522 with
             | (decls,env) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let _0_930 =
                   let _0_929 =
                     primitive_type_axioms env.tcenv lid tname tsym  in
                   FStar_List.append decls _0_929  in
                 (_0_930, env))
      | FStar_Syntax_Syntax.Sig_assume (l,f,uu____10537,uu____10538) ->
          let uu____10541 = encode_formula f env  in
          (match uu____10541 with
           | (f,decls) ->
               let g =
                 let _0_934 =
                   FStar_SMTEncoding_Term.Assume
                     (let _0_933 =
                        Some
                          (let _0_931 = FStar_Syntax_Print.lid_to_string l
                              in
                           FStar_Util.format1 "Assumption: %s" _0_931)
                         in
                      let _0_932 =
                        Some
                          (varops.mk_unique
                             (Prims.strcat "assumption_" l.FStar_Ident.str))
                         in
                      (f, _0_933, _0_932))
                    in
                 [_0_934]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,r,uu____10555,quals,uu____10557)
          when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____10565 =
            FStar_Util.fold_map
              (fun env  ->
                 fun lb  ->
                   let lid =
                     ((FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   let uu____10576 =
                     let _0_935 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone _0_935  in
                   if uu____10576
                   then
                     let val_decl =
                       FStar_Syntax_Syntax.Sig_declare_typ
                         (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp), quals, r)
                        in
                     let uu____10591 = encode_sigelt' env val_decl  in
                     match uu____10591 with | (decls,env) -> (env, decls)
                   else (env, [])) env (Prims.snd lbs)
             in
          (match uu____10565 with
           | (env,decls) -> ((FStar_List.flatten decls), env))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____10608,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t;
                          FStar_Syntax_Syntax.lbunivs = uu____10610;
                          FStar_Syntax_Syntax.lbtyp = uu____10611;
                          FStar_Syntax_Syntax.lbeff = uu____10612;
                          FStar_Syntax_Syntax.lbdef = uu____10613;_}::[]),uu____10614,uu____10615,uu____10616,uu____10617)
          when FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid
          ->
          let uu____10633 =
            new_term_constant_and_tok_from_lid env
              (b2t.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10633 with
           | (tname,ttok,env) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp
                   (let _0_937 =
                      let _0_936 =
                        FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])  in
                      [_0_936]  in
                    ("Valid", _0_937))
                  in
               let decls =
                 let _0_942 =
                   let _0_941 =
                     FStar_SMTEncoding_Term.Assume
                       (let _0_940 =
                          FStar_SMTEncoding_Util.mkForall
                            (let _0_939 =
                               FStar_SMTEncoding_Util.mkEq
                                 (let _0_938 =
                                    FStar_SMTEncoding_Util.mkApp
                                      ("BoxBool_proj_0", [x])
                                     in
                                  (valid_b2t_x, _0_938))
                                in
                             ([[valid_b2t_x]], [xx], _0_939))
                           in
                        (_0_940, (Some "b2t def"), (Some "b2t_def")))
                      in
                   [_0_941]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: _0_942
                  in
               (decls, env))
      | FStar_Syntax_Syntax.Sig_let
          (uu____10672,uu____10673,uu____10674,quals,uu____10676) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___128_10684  ->
                  match uu___128_10684 with
                  | FStar_Syntax_Syntax.Discriminator uu____10685 -> true
                  | uu____10686 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          (uu____10688,uu____10689,lids,quals,uu____10692) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let _0_943 =
                     (FStar_List.hd l.FStar_Ident.ns).FStar_Ident.idText  in
                   _0_943 = "Prims")))
            &&
            (FStar_All.pipe_right quals
               (FStar_Util.for_some
                  (fun uu___129_10702  ->
                     match uu___129_10702 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____10703 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____10706,uu____10707,quals,uu____10709) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___130_10721  ->
                  match uu___130_10721 with
                  | FStar_Syntax_Syntax.Projector uu____10722 -> true
                  | uu____10725 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____10732 = try_lookup_free_var env l  in
          (match uu____10732 with
           | Some uu____10736 -> ([], env)
           | None  ->
               let se =
                 FStar_Syntax_Syntax.Sig_declare_typ
                   (l, (lb.FStar_Syntax_Syntax.lbunivs),
                     (lb.FStar_Syntax_Syntax.lbtyp), quals,
                     (FStar_Ident.range_of_lid l))
                  in
               encode_sigelt env se)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____10744,uu____10745,quals,uu____10747) when
          FStar_All.pipe_right quals
            (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
          ->
          let uu____10759 =
            (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n
             in
          (match uu____10759 with
           | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10764) ->
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
                 let uu____10819 =
                   FStar_Syntax_Util.arrow_formals_comp
                     lb.FStar_Syntax_Syntax.lbtyp
                    in
                 match uu____10819 with
                 | (formals,comp) ->
                     let reified_typ =
                       let _0_944 =
                         FStar_TypeChecker_Env.lcomp_of_comp env.tcenv comp
                          in
                       FStar_TypeChecker_Util.reify_comp
                         (let uu___156_10834 = env.tcenv  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___156_10834.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___156_10834.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___156_10834.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___156_10834.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___156_10834.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___156_10834.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___156_10834.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___156_10834.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___156_10834.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___156_10834.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___156_10834.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___156_10834.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___156_10834.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___156_10834.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___156_10834.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___156_10834.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___156_10834.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___156_10834.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___156_10834.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.type_of =
                              (uu___156_10834.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___156_10834.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___156_10834.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___156_10834.FStar_TypeChecker_Env.qname_and_index)
                          }) _0_944
                        in
                     let _0_945 = FStar_Syntax_Syntax.mk_Total reified_typ
                        in
                     FStar_Syntax_Util.arrow formals _0_945
                  in
               let lb =
                 let uu___157_10836 = lb  in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___157_10836.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___157_10836.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = lb_typ;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___157_10836.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef = tm'
                 }  in
               encode_top_level_let env (false, [lb]) quals
           | uu____10838 -> ([], env))
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____10842,uu____10843,quals,uu____10845) ->
          encode_top_level_let env (is_rec, bindings) quals
      | FStar_Syntax_Syntax.Sig_bundle
          (ses,uu____10859,uu____10860,uu____10861) ->
          let uu____10868 = encode_signature env ses  in
          (match uu____10868 with
           | (g,env) ->
               let uu____10878 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___131_10888  ->
                         match uu___131_10888 with
                         | FStar_SMTEncoding_Term.Assume
                             (uu____10889,Some "inversion axiom",uu____10890)
                             -> false
                         | uu____10894 -> true))
                  in
               (match uu____10878 with
                | (g',inversions) ->
                    let uu____10903 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___132_10913  ->
                              match uu___132_10913 with
                              | FStar_SMTEncoding_Term.DeclFun uu____10914 ->
                                  true
                              | uu____10920 -> false))
                       in
                    (match uu____10903 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____10931,tps,k,uu____10934,datas,quals,uu____10937) ->
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___133_10946  ->
                    match uu___133_10946 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____10947 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____10954 = c  in
              match uu____10954 with
              | (name,args,uu____10958,uu____10959,uu____10960) ->
                  let _0_947 =
                    FStar_SMTEncoding_Term.DeclFun
                      (let _0_946 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____10970  ->
                                 match uu____10970 with
                                 | (uu____10974,sort,uu____10976) -> sort))
                          in
                       (name, _0_946, FStar_SMTEncoding_Term.Term_sort, None))
                     in
                  [_0_947]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____10992 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let _0_948 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right _0_948 FStar_Option.isNone))
               in
            if uu____10992
            then []
            else
              (let uu____11002 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____11002 with
               | (xxsym,xx) ->
                   let uu____11008 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____11019  ->
                             fun l  ->
                               match uu____11019 with
                               | (out,decls) ->
                                   let uu____11031 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____11031 with
                                    | (uu____11037,data_t) ->
                                        let uu____11039 =
                                          FStar_TypeChecker_Util.arrow_formals
                                            env.tcenv data_t
                                           in
                                        (match uu____11039 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____11053 =
                                                 (FStar_Syntax_Subst.compress
                                                    res).FStar_Syntax_Syntax.n
                                                  in
                                               match uu____11053 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____11059,indices) ->
                                                   indices
                                               | uu____11075 -> []  in
                                             let env =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env  ->
                                                       fun uu____11084  ->
                                                         match uu____11084
                                                         with
                                                         | (x,uu____11088) ->
                                                             let _0_950 =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 (let _0_949
                                                                    =
                                                                    mk_term_projector_name
                                                                    l x  in
                                                                  (_0_949,
                                                                    [xx]))
                                                                in
                                                             push_term_var
                                                               env x _0_950)
                                                    env)
                                                in
                                             let uu____11090 =
                                               encode_args indices env  in
                                             (match uu____11090 with
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
                                                      let _0_952 =
                                                        FStar_List.map2
                                                          (fun v  ->
                                                             fun a  ->
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (let _0_951
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                  (_0_951, a)))
                                                          vars indices
                                                         in
                                                      FStar_All.pipe_right
                                                        _0_952
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let _0_955 =
                                                      FStar_SMTEncoding_Util.mkOr
                                                        (let _0_954 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (let _0_953 =
                                                                mk_data_tester
                                                                  env l xx
                                                                 in
                                                              (_0_953, eqs))
                                                            in
                                                         (out, _0_954))
                                                       in
                                                    (_0_955,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____11008 with
                    | (data_ax,decls) ->
                        let uu____11124 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____11124 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let _0_956 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     _0_956 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               FStar_SMTEncoding_Term.Assume
                                 (let _0_960 =
                                    FStar_SMTEncoding_Util.mkForall
                                      (let _0_958 =
                                         add_fuel
                                           (ffsym,
                                             FStar_SMTEncoding_Term.Fuel_sort)
                                           ((xxsym,
                                              FStar_SMTEncoding_Term.Term_sort)
                                           :: vars)
                                          in
                                       let _0_957 =
                                         FStar_SMTEncoding_Util.mkImp
                                           (xx_has_type_sfuel, data_ax)
                                          in
                                       ([[xx_has_type_sfuel]], _0_958,
                                         _0_957))
                                     in
                                  let _0_959 =
                                    Some
                                      (varops.mk_unique
                                         (Prims.strcat
                                            "fuel_guarded_inversion_"
                                            t.FStar_Ident.str))
                                     in
                                  (_0_960, (Some "inversion axiom"), _0_959))
                                in
                             let pattern_guarded_inversion =
                               let uu____11152 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____11152
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let _0_965 =
                                   FStar_SMTEncoding_Term.Assume
                                     (let _0_964 =
                                        FStar_SMTEncoding_Util.mkForall
                                          (let _0_962 =
                                             add_fuel
                                               (ffsym,
                                                 FStar_SMTEncoding_Term.Fuel_sort)
                                               ((xxsym,
                                                  FStar_SMTEncoding_Term.Term_sort)
                                               :: vars)
                                              in
                                           let _0_961 =
                                             FStar_SMTEncoding_Util.mkImp
                                               (xx_has_type_fuel, data_ax)
                                              in
                                           ([[xx_has_type_fuel;
                                             pattern_guard]], _0_962, _0_961))
                                         in
                                      let _0_963 =
                                        Some
                                          (varops.mk_unique
                                             (Prims.strcat
                                                "pattern_guarded_inversion_"
                                                t.FStar_Ident.str))
                                         in
                                      (_0_964, (Some "inversion axiom"),
                                        _0_963))
                                    in
                                 [_0_965]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____11174 =
            let uu____11180 =
              (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n  in
            match uu____11180 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                let _0_966 = FStar_TypeChecker_Env.result_typ env.tcenv kres
                   in
                ((FStar_List.append tps formals), _0_966)
            | uu____11203 -> (tps, k)  in
          (match uu____11174 with
           | (formals,res) ->
               let uu____11214 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____11214 with
                | (formals,res) ->
                    let uu____11221 = encode_binders None formals env  in
                    (match uu____11221 with
                     | (vars,guards,env',binder_decls,uu____11236) ->
                         let uu____11243 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____11243 with
                          | (tname,ttok,env) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (let _0_967 =
                                     FStar_List.map
                                       FStar_SMTEncoding_Util.mkFreeV vars
                                      in
                                   (tname, _0_967))
                                 in
                              let uu____11259 =
                                let tname_decl =
                                  constructor_or_logic_type_decl
                                    (let _0_969 =
                                       FStar_All.pipe_right vars
                                         (FStar_List.map
                                            (fun uu____11279  ->
                                               match uu____11279 with
                                               | (n,s) ->
                                                   ((Prims.strcat tname n),
                                                     s, false)))
                                        in
                                     let _0_968 = varops.next_id ()  in
                                     (tname, _0_969,
                                       FStar_SMTEncoding_Term.Term_sort,
                                       _0_968, false))
                                   in
                                let uu____11287 =
                                  match vars with
                                  | [] ->
                                      let _0_973 =
                                        let _0_972 =
                                          let _0_971 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_970  -> Some _0_970)
                                            _0_971
                                           in
                                        push_free_var env t tname _0_972  in
                                      ([], _0_973)
                                  | uu____11297 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let _0_974 = varops.next_id ()  in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          _0_974
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        FStar_SMTEncoding_Term.Assume
                                          (let _0_976 =
                                             FStar_SMTEncoding_Util.mkForall'
                                               (let _0_975 =
                                                  FStar_SMTEncoding_Util.mkEq
                                                    (ttok_app, tapp)
                                                   in
                                                (pats, None, vars, _0_975))
                                              in
                                           (_0_976,
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
                                match uu____11287 with
                                | (tok_decls,env) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env)
                                 in
                              (match uu____11259 with
                               | (decls,env) ->
                                   let kindingAx =
                                     let uu____11334 =
                                       encode_term_pred None res env' tapp
                                        in
                                     match uu____11334 with
                                     | (k,decls) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals) >
                                               (Prims.parse_int "0")
                                           then
                                             let _0_979 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_978 =
                                                    let _0_977 =
                                                      FStar_SMTEncoding_Term.mk_PreType
                                                        ttok_tm
                                                       in
                                                    FStar_SMTEncoding_Term.mk_tester
                                                      "Tm_arrow" _0_977
                                                     in
                                                  (_0_978, (Some "kinding"),
                                                    (Some
                                                       (Prims.strcat
                                                          "pre_kinding_" ttok))))
                                                in
                                             [_0_979]
                                           else []  in
                                         let _0_984 =
                                           let _0_983 =
                                             let _0_982 =
                                               FStar_SMTEncoding_Term.Assume
                                                 (let _0_981 =
                                                    FStar_SMTEncoding_Util.mkForall
                                                      (let _0_980 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, k)
                                                          in
                                                       ([[tapp]], vars,
                                                         _0_980))
                                                     in
                                                  (_0_981, None,
                                                    (Some
                                                       (Prims.strcat
                                                          "kinding_" ttok))))
                                                in
                                             [_0_982]  in
                                           FStar_List.append karr _0_983  in
                                         FStar_List.append decls _0_984
                                      in
                                   let aux =
                                     let _0_988 =
                                       let _0_987 =
                                         inversion_axioms tapp vars  in
                                       let _0_986 =
                                         let _0_985 = pretype_axiom tapp vars
                                            in
                                         [_0_985]  in
                                       FStar_List.append _0_987 _0_986  in
                                     FStar_List.append kindingAx _0_988  in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11364,uu____11365,uu____11366,uu____11367,uu____11368,uu____11369,uu____11370)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____11377,t,uu____11379,n_tps,quals,uu____11382,drange) ->
          let uu____11388 = new_term_constant_and_tok_from_lid env d  in
          (match uu____11388 with
           | (ddconstrsym,ddtok,env) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____11399 =
                 FStar_TypeChecker_Util.arrow_formals env.tcenv t  in
               (match uu____11399 with
                | (formals,t_res) ->
                    let uu____11406 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____11406 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____11415 =
                           encode_binders (Some fuel_tm) formals env  in
                         (match uu____11415 with
                          | (vars,guards,env',binder_decls,names) ->
                              let fields =
                                FStar_All.pipe_right names
                                  (FStar_List.mapi
                                     (fun n  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let _0_989 =
                                            mk_term_projector_name d x  in
                                          (_0_989,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let _0_991 =
                                  let _0_990 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort, _0_990,
                                    true)
                                   in
                                FStar_All.pipe_right _0_991
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
                              let uu____11475 =
                                encode_term_pred None t env ddtok_tm  in
                              (match uu____11475 with
                               | (tok_typing,decls3) ->
                                   let uu____11482 =
                                     encode_binders (Some fuel_tm) formals
                                       env
                                      in
                                   (match uu____11482 with
                                    | (vars',guards',env'',decls_formals,uu____11497)
                                        ->
                                        let uu____11504 =
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
                                        (match uu____11504 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____11523 ->
                                                   let _0_993 =
                                                     let _0_992 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       _0_992
                                                      in
                                                   [_0_993]
                                                in
                                             let encode_elim uu____11530 =
                                               let uu____11531 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____11531 with
                                               | (head,args) ->
                                                   let uu____11560 =
                                                     (FStar_Syntax_Subst.compress
                                                        head).FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____11560 with
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
                                                        let uu____11576 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____11576
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
                                                                 | uu____11602
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
                                                                    let uu____11610
                                                                    =
                                                                    let _0_994
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv _0_994
                                                                     in
                                                                    if
                                                                    uu____11610
                                                                    then
                                                                    let _0_995
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv xv
                                                                     in
                                                                    [_0_995]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards
                                                                in
                                                             let uu____11615
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____11628
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____11628
                                                                    with
                                                                    | 
                                                                    (env,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____11650
                                                                    =
                                                                    let _0_996
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env
                                                                    _0_996
                                                                     in
                                                                    (match uu____11650
                                                                    with
                                                                    | 
                                                                    (uu____11660,xv,env)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let _0_997
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    _0_997 ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let _0_998
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    _0_998 ::
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
                                                             (match uu____11615
                                                              with
                                                              | (uu____11674,arg_vars,elim_eqns_or_guards,uu____11677)
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
                                                                    (let _0_1002
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1001
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_1000
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_999
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    _0_999))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_1001,
                                                                    _0_1000))
                                                                     in
                                                                    (_0_1002,
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
                                                                    let _0_1003
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (_0_1003,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1011
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1009
                                                                    =
                                                                    let _0_1005
                                                                    =
                                                                    let _0_1004
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    [_0_1004]
                                                                     in
                                                                    [_0_1005]
                                                                     in
                                                                    let _0_1008
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_1007
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let _0_1006
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp
                                                                     in
                                                                    (_0_1007,
                                                                    _0_1006))
                                                                     in
                                                                    (_0_1009,
                                                                    [x],
                                                                    _0_1008))
                                                                     in
                                                                    let _0_1010
                                                                    =
                                                                    Some
                                                                    (varops.mk_unique
                                                                    "lextop")
                                                                     in
                                                                    (_0_1011,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    _0_1010))
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let _0_1014
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
                                                                    (let _0_1013
                                                                    =
                                                                    let _0_1012
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    _0_1012
                                                                    dapp  in
                                                                    [_0_1013])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    _0_1014
                                                                    FStar_List.flatten
                                                                     in
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1017
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let _0_1016
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (let _0_1015
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    _0_1015))
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    _0_1017,
                                                                    _0_1016))
                                                                     in
                                                                    (_0_1018,
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
                                                    | uu____11755 ->
                                                        ((let _0_1021 =
                                                            let _0_1020 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let _0_1019 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              _0_1020 _0_1019
                                                             in
                                                          FStar_Errors.warn
                                                            drange _0_1021);
                                                         ([], [])))
                                                in
                                             let uu____11759 = encode_elim ()
                                                in
                                             (match uu____11759 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let _0_1042 =
                                                      let _0_1041 =
                                                        let _0_1040 =
                                                          let _0_1039 =
                                                            let _0_1024 =
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                (let _0_1023
                                                                   =
                                                                   Some
                                                                    (let _0_1022
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    _0_1022)
                                                                    in
                                                                 (ddtok, [],
                                                                   FStar_SMTEncoding_Term.Term_sort,
                                                                   _0_1023))
                                                               in
                                                            [_0_1024]  in
                                                          let _0_1038 =
                                                            let _0_1037 =
                                                              let _0_1036 =
                                                                let _0_1035 =
                                                                  let _0_1034
                                                                    =
                                                                    let _0_1033
                                                                    =
                                                                    let _0_1032
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1026
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1025
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    _0_1025))
                                                                     in
                                                                    (_0_1026,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))))
                                                                     in
                                                                    let _0_1031
                                                                    =
                                                                    let _0_1030
                                                                    =
                                                                    FStar_SMTEncoding_Term.Assume
                                                                    (let _0_1029
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    (let _0_1028
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let _0_1027
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    _0_1028,
                                                                    _0_1027))
                                                                     in
                                                                    (_0_1029,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Some
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))))
                                                                     in
                                                                    [_0_1030]
                                                                     in
                                                                    _0_1032
                                                                    ::
                                                                    _0_1031
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
                                                                    _0_1033
                                                                     in
                                                                  FStar_List.append
                                                                    _0_1034
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  _0_1035
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                _0_1036
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              _0_1037
                                                             in
                                                          FStar_List.append
                                                            _0_1039 _0_1038
                                                           in
                                                        FStar_List.append
                                                          decls3 _0_1040
                                                         in
                                                      FStar_List.append
                                                        decls2 _0_1041
                                                       in
                                                    FStar_List.append
                                                      binder_decls _0_1042
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
           (fun uu____11804  ->
              fun se  ->
                match uu____11804 with
                | (g,env) ->
                    let uu____11816 = encode_sigelt env se  in
                    (match uu____11816 with
                     | (g',env) -> ((FStar_List.append g g'), env)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____11852 =
        match uu____11852 with
        | (i,decls,env) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____11870 ->
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
                 ((let uu____11875 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____11875
                   then
                     let _0_1045 = FStar_Syntax_Print.bv_to_string x  in
                     let _0_1044 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let _0_1043 = FStar_Syntax_Print.term_to_string t1  in
                     FStar_Util.print3 "Normalized %s : %s to %s\n" _0_1045
                       _0_1044 _0_1043
                   else ());
                  (let uu____11877 = encode_term t1 env  in
                   match uu____11877 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____11887 =
                         let _0_1050 =
                           let _0_1049 =
                             let _0_1048 = FStar_Util.digest_of_string t_hash
                                in
                             let _0_1047 =
                               let _0_1046 = FStar_Util.string_of_int i  in
                               Prims.strcat "_" _0_1046  in
                             Prims.strcat _0_1048 _0_1047  in
                           Prims.strcat "x_" _0_1049  in
                         new_term_constant_from_string env x _0_1050  in
                       (match uu____11887 with
                        | (xxsym,xx,env') ->
                            let t =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____11901 = FStar_Options.log_queries ()
                                 in
                              if uu____11901
                              then
                                Some
                                  (let _0_1053 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let _0_1052 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let _0_1051 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3 "%s : %s (%s)" _0_1053
                                     _0_1052 _0_1051)
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____11915,t)) ->
                 let t_norm = whnf env t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____11924 = encode_free_var env fv t t_norm []  in
                 (match uu____11924 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____11943 = encode_sigelt env se  in
                 (match uu____11943 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____11953 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____11953 with | (uu____11965,decls,env) -> (decls, env)
  
let encode_labels labs =
  let prefix =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____12010  ->
            match uu____12010 with
            | (l,uu____12017,uu____12018) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____12039  ->
            match uu____12039 with
            | (l,uu____12047,uu____12048) ->
                let _0_1057 =
                  FStar_All.pipe_left
                    (fun _0_1054  -> FStar_SMTEncoding_Term.Echo _0_1054)
                    (Prims.fst l)
                   in
                let _0_1056 =
                  let _0_1055 =
                    FStar_SMTEncoding_Term.Eval
                      (FStar_SMTEncoding_Util.mkFreeV l)
                     in
                  [_0_1055]  in
                _0_1057 :: _0_1056))
     in
  (prefix, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let _0_1060 =
      let _0_1059 =
        let _0_1058 = FStar_Util.smap_create (Prims.parse_int "100")  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = _0_1058;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true
        }  in
      [_0_1059]  in
    FStar_ST.write last_env _0_1060
  
let get_env : FStar_TypeChecker_Env.env -> env_t =
  fun tcenv  ->
    let uu____12074 = FStar_ST.read last_env  in
    match uu____12074 with
    | [] -> failwith "No env; call init first!"
    | e::uu____12080 ->
        let uu___158_12082 = e  in
        {
          bindings = (uu___158_12082.bindings);
          depth = (uu___158_12082.depth);
          tcenv;
          warn = (uu___158_12082.warn);
          cache = (uu___158_12082.cache);
          nolabels = (uu___158_12082.nolabels);
          use_zfuel_name = (uu___158_12082.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___158_12082.encode_non_total_function_typ)
        }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____12086 = FStar_ST.read last_env  in
    match uu____12086 with
    | [] -> failwith "Empty env stack"
    | uu____12091::tl -> FStar_ST.write last_env (env :: tl)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____12099  ->
    let uu____12100 = FStar_ST.read last_env  in
    match uu____12100 with
    | [] -> failwith "Empty env stack"
    | hd::tl ->
        let refs = FStar_Util.smap_copy hd.cache  in
        let top =
          let uu___159_12121 = hd  in
          {
            bindings = (uu___159_12121.bindings);
            depth = (uu___159_12121.depth);
            tcenv = (uu___159_12121.tcenv);
            warn = (uu___159_12121.warn);
            cache = refs;
            nolabels = (uu___159_12121.nolabels);
            use_zfuel_name = (uu___159_12121.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___159_12121.encode_non_total_function_typ)
          }  in
        FStar_ST.write last_env (top :: hd :: tl)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____12127  ->
    let uu____12128 = FStar_ST.read last_env  in
    match uu____12128 with
    | [] -> failwith "Popping an empty stack"
    | uu____12133::tl -> FStar_ST.write last_env tl
  
let mark_env : Prims.unit -> Prims.unit = fun uu____12141  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____12144  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____12147  ->
    let uu____12148 = FStar_ST.read last_env  in
    match uu____12148 with
    | hd::uu____12154::tl -> FStar_ST.write last_env (hd :: tl)
    | uu____12160 -> failwith "Impossible"
  
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
        let uu____12205 = FStar_Options.log_queries ()  in
        if uu____12205
        then
          let _0_1063 =
            FStar_SMTEncoding_Term.Caption
              (let _0_1062 =
                 let _0_1061 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                     (FStar_List.map FStar_Syntax_Print.lid_to_string)
                    in
                 FStar_All.pipe_right _0_1061 (FStar_String.concat ", ")  in
               Prims.strcat "encoding sigelt " _0_1062)
             in
          _0_1063 :: decls
        else decls  in
      let env = get_env tcenv  in
      let uu____12212 = encode_sigelt env se  in
      match uu____12212 with
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
      (let uu____12227 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____12227
       then
         let _0_1064 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             FStar_Util.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           _0_1064
       else ());
      (let env = get_env tcenv  in
       let uu____12232 =
         encode_signature
           (let uu___160_12236 = env  in
            {
              bindings = (uu___160_12236.bindings);
              depth = (uu___160_12236.depth);
              tcenv = (uu___160_12236.tcenv);
              warn = false;
              cache = (uu___160_12236.cache);
              nolabels = (uu___160_12236.nolabels);
              use_zfuel_name = (uu___160_12236.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_12236.encode_non_total_function_typ)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____12232 with
       | (decls,env) ->
           let caption decls =
             let uu____12248 = FStar_Options.log_queries ()  in
             if uu____12248
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls  in
           (set_env
              (let uu___161_12253 = env  in
               {
                 bindings = (uu___161_12253.bindings);
                 depth = (uu___161_12253.depth);
                 tcenv = (uu___161_12253.tcenv);
                 warn = true;
                 cache = (uu___161_12253.cache);
                 nolabels = (uu___161_12253.nolabels);
                 use_zfuel_name = (uu___161_12253.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_12253.encode_non_total_function_typ)
               });
            (let uu____12255 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____12255
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
         let uu____12297 =
           let rec aux bindings =
             match bindings with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____12318 = aux rest  in
                 (match uu____12318 with
                  | (out,rest) ->
                      let t =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv x.FStar_Syntax_Syntax.sort
                         in
                      let _0_1066 =
                        let _0_1065 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_12336 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_12336.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_12336.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t
                             })
                           in
                        _0_1065 :: out  in
                      (_0_1066, rest))
             | uu____12337 -> ([], bindings)  in
           let uu____12341 = aux bindings  in
           match uu____12341 with
           | (closing,bindings) ->
               let _0_1067 =
                 FStar_Syntax_Util.close_forall (FStar_List.rev closing) q
                  in
               (_0_1067, bindings)
            in
         match uu____12297 with
         | (q,bindings) ->
             let uu____12367 =
               let _0_1068 =
                 FStar_List.filter
                   (fun uu___134_12370  ->
                      match uu___134_12370 with
                      | FStar_TypeChecker_Env.Binding_sig uu____12371 ->
                          false
                      | uu____12375 -> true) bindings
                  in
               encode_env_bindings env _0_1068  in
             (match uu____12367 with
              | (env_decls,env) ->
                  ((let uu____12386 =
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
                    if uu____12386
                    then
                      let _0_1069 = FStar_Syntax_Print.term_to_string q  in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        _0_1069
                    else ());
                   (let uu____12388 = encode_formula q env  in
                    match uu____12388 with
                    | (phi,qdecls) ->
                        let uu____12400 =
                          let _0_1070 = FStar_TypeChecker_Env.get_range tcenv
                             in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg _0_1070 phi
                           in
                        (match uu____12400 with
                         | (labels,phi) ->
                             let uu____12412 = encode_labels labels  in
                             (match uu____12412 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    FStar_SMTEncoding_Term.Assume
                                      (let _0_1072 =
                                         FStar_SMTEncoding_Util.mkNot phi  in
                                       let _0_1071 =
                                         Some (varops.mk_unique "@query")  in
                                       (_0_1072, (Some "query"), _0_1071))
                                     in
                                  let suffix =
                                    let _0_1074 =
                                      let _0_1073 =
                                        let uu____12437 =
                                          FStar_Options.print_z3_statistics
                                            ()
                                           in
                                        if uu____12437
                                        then
                                          [FStar_SMTEncoding_Term.PrintStats]
                                        else []  in
                                      FStar_List.append _0_1073
                                        [FStar_SMTEncoding_Term.Echo "Done!"]
                                       in
                                    FStar_List.append label_suffix _0_1074
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env = get_env tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____12450 = encode_formula q env  in
       match uu____12450 with
       | (f,uu____12454) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____12456) -> true
             | uu____12459 -> false)))
  