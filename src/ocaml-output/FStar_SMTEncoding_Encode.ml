open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives ()  in
  if uu____16 then tl1 else x :: tl1 
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c) 
let vargs args =
  FStar_List.filter
    (fun uu___101_74  ->
       match uu___101_74 with
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
        let uu___126_140 = a  in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___126_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_140.FStar_Syntax_Syntax.sort)
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
                         mk_term_projector_name lid (fst b)))
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
  let new_scope uu____433 =
    let uu____434 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____436 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____434, uu____436)  in
  let scopes =
    let uu____447 = let uu____453 = new_scope ()  in [uu____453]  in
    FStar_Util.mk_ref uu____447  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____478 =
        let uu____480 = FStar_ST.read scopes  in
        FStar_Util.find_map uu____480
          (fun uu____497  ->
             match uu____497 with
             | (names1,uu____504) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____478 with
      | None  -> y1
      | Some uu____509 ->
          (FStar_Util.incr ctr;
           (let uu____514 =
              let uu____515 =
                let uu____516 = FStar_ST.read ctr  in
                Prims.string_of_int uu____516  in
              Prims.strcat "__" uu____515  in
            Prims.strcat y1 uu____514))
       in
    let top_scope =
      let uu____521 =
        let uu____526 = FStar_ST.read scopes  in FStar_List.hd uu____526  in
      FStar_All.pipe_left FStar_Pervasives.fst uu____521  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____565 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh1 pfx =
    let uu____576 =
      let uu____577 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____577  in
    FStar_Util.format2 "%s_%s" pfx uu____576  in
  let string_const s =
    let uu____582 =
      let uu____584 = FStar_ST.read scopes  in
      FStar_Util.find_map uu____584
        (fun uu____601  ->
           match uu____601 with
           | (uu____607,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____582 with
    | Some f -> f
    | None  ->
        let id = next_id1 ()  in
        let f =
          let uu____616 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____616  in
        let top_scope =
          let uu____619 =
            let uu____624 = FStar_ST.read scopes  in FStar_List.hd uu____624
             in
          FStar_All.pipe_left FStar_Pervasives.snd uu____619  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____652 =
    let uu____653 =
      let uu____659 = new_scope ()  in
      let uu____664 = FStar_ST.read scopes  in uu____659 :: uu____664  in
    FStar_ST.write scopes uu____653  in
  let pop1 uu____691 =
    let uu____692 =
      let uu____698 = FStar_ST.read scopes  in FStar_List.tl uu____698  in
    FStar_ST.write scopes uu____692  in
  let mark1 uu____725 = push1 ()  in
  let reset_mark1 uu____729 = pop1 ()  in
  let commit_mark1 uu____733 =
    let uu____734 = FStar_ST.read scopes  in
    match uu____734 with
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
    | uu____794 -> failwith "Impossible"  in
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
    let uu___127_803 = x  in
    let uu____804 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____804;
      FStar_Syntax_Syntax.index = (uu___127_803.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_803.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) 
  | Binding_fvar of (FStar_Ident.lident * Prims.string *
  FStar_SMTEncoding_Term.term option * FStar_SMTEncoding_Term.term option) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____827 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____851 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term option *
      FStar_SMTEncoding_Term.term option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar v1 = (v1, None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___102_1039  ->
            match uu___102_1039 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1042 -> []))
     in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  } 
let use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let print_env : env_t -> Prims.string =
  fun e  ->
    let uu____1050 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1054  ->
              match uu___103_1054 with
              | Binding_var (x,uu____1056) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1058,uu____1059,uu____1060) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____1050 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t : env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1093 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____1093
      then
        let uu____1095 = FStar_Syntax_Print.term_to_string t  in
        Some uu____1095
      else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____1106 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____1106)
  
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
        (let uu___128_1118 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1118.tcenv);
           warn = (uu___128_1118.warn);
           cache = (uu___128_1118.cache);
           nolabels = (uu___128_1118.nolabels);
           use_zfuel_name = (uu___128_1118.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1118.encode_non_total_function_typ);
           current_module_name = (uu___128_1118.current_module_name)
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
        (let uu___129_1131 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1131.depth);
           tcenv = (uu___129_1131.tcenv);
           warn = (uu___129_1131.warn);
           cache = (uu___129_1131.cache);
           nolabels = (uu___129_1131.nolabels);
           use_zfuel_name = (uu___129_1131.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1131.encode_non_total_function_typ);
           current_module_name = (uu___129_1131.current_module_name)
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
          (let uu___130_1147 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1147.depth);
             tcenv = (uu___130_1147.tcenv);
             warn = (uu___130_1147.warn);
             cache = (uu___130_1147.cache);
             nolabels = (uu___130_1147.nolabels);
             use_zfuel_name = (uu___130_1147.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1147.encode_non_total_function_typ);
             current_module_name = (uu___130_1147.current_module_name)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1157 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1157.depth);
          tcenv = (uu___131_1157.tcenv);
          warn = (uu___131_1157.warn);
          cache = (uu___131_1157.cache);
          nolabels = (uu___131_1157.nolabels);
          use_zfuel_name = (uu___131_1157.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1157.encode_non_total_function_typ);
          current_module_name = (uu___131_1157.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1173  ->
             match uu___104_1173 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1181 -> None)
         in
      let uu____1184 = aux a  in
      match uu____1184 with
      | None  ->
          let a2 = unmangle a  in
          let uu____1191 = aux a2  in
          (match uu____1191 with
           | None  ->
               let uu____1197 =
                 let uu____1198 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____1199 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1198 uu____1199
                  in
               failwith uu____1197
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____1219 =
        let uu___132_1220 = env  in
        let uu____1221 =
          let uu____1223 =
            let uu____1224 =
              let uu____1231 =
                let uu____1233 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1233  in
              (x, fname, uu____1231, None)  in
            Binding_fvar uu____1224  in
          uu____1223 :: (env.bindings)  in
        {
          bindings = uu____1221;
          depth = (uu___132_1220.depth);
          tcenv = (uu___132_1220.tcenv);
          warn = (uu___132_1220.warn);
          cache = (uu___132_1220.cache);
          nolabels = (uu___132_1220.nolabels);
          use_zfuel_name = (uu___132_1220.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1220.encode_non_total_function_typ);
          current_module_name = (uu___132_1220.current_module_name)
        }  in
      (fname, ftok, uu____1219)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term option *
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1255  ->
           match uu___105_1255 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1277 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1289 =
        lookup_binding env
          (fun uu___106_1291  ->
             match uu___106_1291 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1301 -> None)
         in
      FStar_All.pipe_right uu____1289 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term option *
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1314 = try_lookup_lid env a  in
      match uu____1314 with
      | None  ->
          let uu____1331 =
            let uu____1332 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____1332  in
          failwith uu____1331
      | Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1363 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1363.depth);
            tcenv = (uu___133_1363.tcenv);
            warn = (uu___133_1363.warn);
            cache = (uu___133_1363.cache);
            nolabels = (uu___133_1363.nolabels);
            use_zfuel_name = (uu___133_1363.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1363.encode_non_total_function_typ);
            current_module_name = (uu___133_1363.current_module_name)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1375 = lookup_lid env x  in
        match uu____1375 with
        | (t1,t2,uu____1383) ->
            let t3 =
              let uu____1389 =
                let uu____1393 =
                  let uu____1395 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____1395]  in
                (f, uu____1393)  in
              FStar_SMTEncoding_Util.mkApp uu____1389  in
            let uu___134_1398 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1398.depth);
              tcenv = (uu___134_1398.tcenv);
              warn = (uu___134_1398.warn);
              cache = (uu___134_1398.cache);
              nolabels = (uu___134_1398.nolabels);
              use_zfuel_name = (uu___134_1398.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1398.encode_non_total_function_typ);
              current_module_name = (uu___134_1398.current_module_name)
            }
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1408 = try_lookup_lid env l  in
      match uu____1408 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1435 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1440,fuel::[]) ->
                         let uu____1443 =
                           let uu____1444 =
                             let uu____1445 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____1445
                               FStar_Pervasives.fst
                              in
                           FStar_Util.starts_with uu____1444 "fuel"  in
                         if uu____1443
                         then
                           let uu____1447 =
                             let uu____1448 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1448
                               fuel
                              in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1447
                         else Some t
                     | uu____1451 -> Some t)
                | uu____1452 -> None))
  
let lookup_free_var env a =
  let uu____1470 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____1470 with
  | Some t -> t
  | None  ->
      let uu____1473 =
        let uu____1474 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format1 "Name not found: %s" uu____1474  in
      failwith uu____1473
  
let lookup_free_var_name env a =
  let uu____1491 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1491 with | (x,uu____1498,uu____1499) -> x 
let lookup_free_var_sym env a =
  let uu____1523 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____1523 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1544;
             FStar_SMTEncoding_Term.rng = uu____1545;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1553 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1567 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name : env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1576  ->
           match uu___107_1576 with
           | Binding_fvar (uu____1578,nm',tok,uu____1581) when nm = nm' ->
               tok
           | uu____1586 -> None)
  
let mkForall_fuel' n1 uu____1603 =
  match uu____1603 with
  | (pats,vars,body) ->
      let fallback uu____1619 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____1622 = FStar_Options.unthrottle_inductives ()  in
      if uu____1622
      then fallback ()
      else
        (let uu____1624 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
         match uu____1624 with
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
                       | uu____1643 -> p))
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
                         let uu____1657 = add_fuel1 guards  in
                         FStar_SMTEncoding_Util.mk_and_l uu____1657
                     | uu____1659 ->
                         let uu____1660 = add_fuel1 [guard]  in
                         FStar_All.pipe_right uu____1660 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1663 -> body  in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1689 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1697 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1702 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1703 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1712 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1727 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1729 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1729 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1743;
             FStar_Syntax_Syntax.pos = uu____1744;
             FStar_Syntax_Syntax.vars = uu____1745;_},uu____1746)
          ->
          let uu____1761 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1761 FStar_Option.isNone
      | uu____1774 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1781 =
        let uu____1782 = FStar_Syntax_Util.un_uinst t  in
        uu____1782.FStar_Syntax_Syntax.n  in
      match uu____1781 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1785,uu____1786,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1815  ->
                  match uu___108_1815 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1816 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1817,uu____1818,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1845 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____1845 FStar_Option.isSome
      | uu____1858 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1865 = head_normal env t  in
      if uu____1865
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
    let uu____1876 =
      let uu____1877 = FStar_Syntax_Syntax.null_binder t  in [uu____1877]  in
    let uu____1878 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____1876 uu____1878 None
  
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
                match snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1905 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1905
                | s ->
                    let uu____1908 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1908) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1920  ->
    match uu___109_1920 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1921 -> false
  
let is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____1949;
                       FStar_SMTEncoding_Term.rng = uu____1950;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1964) ->
              let uu____1969 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1979 -> false) args (FStar_List.rev xs))
                 in
              if uu____1969 then tok_of_name env f else None
          | (uu____1982,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____1985 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1987 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____1987))
                 in
              if uu____1985 then Some t else None
          | uu____1990 -> None  in
        check_partial_applications body (FStar_List.rev vars)
  
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
    | uu____2081 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2084  ->
    match uu___110_2084 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2086 =
          let uu____2090 =
            let uu____2092 =
              let uu____2093 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____2093  in
            [uu____2092]  in
          ("FStar.Char.Char", uu____2090)  in
        FStar_SMTEncoding_Util.mkApp uu____2086
    | FStar_Const.Const_int (i,None ) ->
        let uu____2101 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____2101
    | FStar_Const.Const_int (i,Some uu____2103) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2112) ->
        let uu____2115 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____2115
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2119 =
          let uu____2120 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____2120  in
        failwith uu____2119
  
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2139 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2147 ->
            let uu____2152 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2152
        | uu____2153 ->
            if norm1
            then let uu____2154 = whnf env t1  in aux false uu____2154
            else
              (let uu____2156 =
                 let uu____2157 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2158 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2157 uu____2158
                  in
               failwith uu____2156)
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
    | uu____2179 ->
        let uu____2180 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2180)
  
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2208::uu____2209::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2212::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2214 -> false 
let rec encode_binders :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * env_t * FStar_SMTEncoding_Term.decls_t *
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2352 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____2352
         then
           let uu____2353 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____2353
         else ());
        (let uu____2355 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2391  ->
                   fun b  ->
                     match uu____2391 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2434 =
                           let x = unmangle (fst b)  in
                           let uu____2443 = gen_term_var env1 x  in
                           match uu____2443 with
                           | (xxsym,xx,env') ->
                               let uu____2457 =
                                 let uu____2460 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____2460 env1 xx
                                  in
                               (match uu____2457 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____2434 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____2355 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and encode_term_pred :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2548 = encode_term t env  in
          match uu____2548 with
          | (t1,decls) ->
              let uu____2555 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____2555, decls)

and encode_term_pred' :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2563 = encode_term t env  in
          match uu____2563 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2572 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____2572, decls)
               | Some f ->
                   let uu____2574 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____2574, decls))

and encode_arith_term :
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2580 = encode_args args_e env  in
        match uu____2580 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2592 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____2599 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____2599  in
            let binary arg_tms1 =
              let uu____2608 =
                let uu____2609 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____2609  in
              let uu____2610 =
                let uu____2611 =
                  let uu____2612 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____2612  in
                FStar_SMTEncoding_Term.unboxInt uu____2611  in
              (uu____2608, uu____2610)  in
            let mk_default uu____2617 =
              let uu____2618 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____2618 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l op mk_args ts =
              let uu____2663 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____2663
              then
                let uu____2664 =
                  let uu____2665 = mk_args ts  in op uu____2665  in
                FStar_All.pipe_right uu____2664 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____2688 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____2688
              then
                let uu____2689 = binary ts  in
                match uu____2689 with
                | (t1,t2) ->
                    let uu____2694 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____2694
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2697 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____2697
                 then
                   let uu____2698 = op (binary ts)  in
                   FStar_All.pipe_right uu____2698
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)]  in
            let uu____2788 =
              let uu____2794 =
                FStar_List.tryFind
                  (fun uu____2806  ->
                     match uu____2806 with
                     | (l,uu____2813) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____2794 FStar_Util.must  in
            (match uu____2788 with
             | (uu____2838,op) ->
                 let uu____2846 = op arg_tms  in (uu____2846, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____2853 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____2853
       then
         let uu____2854 = FStar_Syntax_Print.tag_of_term t  in
         let uu____2855 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____2856 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2854 uu____2855
           uu____2856
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2860 ->
           let uu____2881 =
             let uu____2882 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2883 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2884 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2885 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2882
               uu____2883 uu____2884 uu____2885
              in
           failwith uu____2881
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2888 =
             let uu____2889 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____2890 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____2891 = FStar_Syntax_Print.term_to_string t0  in
             let uu____2892 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2889
               uu____2890 uu____2891 uu____2892
              in
           failwith uu____2888
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2896 =
             let uu____2897 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2897
              in
           failwith uu____2896
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2902) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2932) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2941 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____2941, [])
       | FStar_Syntax_Syntax.Tm_type uu____2947 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2950) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2956 = encode_const c  in (uu____2956, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____2971 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____2971 with
            | (binders1,res) ->
                let uu____2978 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____2978
                then
                  let uu____2981 = encode_binders None binders1 env  in
                  (match uu____2981 with
                   | (vars,guards,env',decls,uu____2996) ->
                       let fsym =
                         let uu____3006 = varops.fresh "f"  in
                         (uu____3006, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3009 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3013 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3013.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3013.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3013.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3013.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3013.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3013.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3013.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3013.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3013.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3013.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3013.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3013.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3013.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3013.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3013.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3013.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3013.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3013.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3013.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3013.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3013.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3013.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3013.FStar_TypeChecker_Env.qname_and_index)
                            }) res
                          in
                       (match uu____3009 with
                        | (pre_opt,res_t) ->
                            let uu____3020 =
                              encode_term_pred None res_t env' app  in
                            (match uu____3020 with
                             | (res_pred,decls') ->
                                 let uu____3027 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3034 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____3034, [])
                                   | Some pre ->
                                       let uu____3037 =
                                         encode_formula pre env'  in
                                       (match uu____3037 with
                                        | (guard,decls0) ->
                                            let uu____3045 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____3045, decls0))
                                    in
                                 (match uu____3027 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3053 =
                                          let uu____3059 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____3059)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3053
                                         in
                                      let cvars =
                                        let uu____3069 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____3069
                                          (FStar_List.filter
                                             (fun uu____3075  ->
                                                match uu____3075 with
                                                | (x,uu____3079) ->
                                                    x <> (fst fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____3090 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____3090 with
                                       | Some cache_entry ->
                                           let uu____3095 =
                                             let uu____3096 =
                                               let uu____3100 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3100)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3096
                                              in
                                           (uu____3095,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3111 =
                                               let uu____3112 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3112
                                                in
                                             varops.mk_unique uu____3111  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars
                                              in
                                           let caption =
                                             let uu____3119 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____3119
                                             then
                                               let uu____3121 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____3121
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____3127 =
                                               let uu____3131 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____3131)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3127
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
                                             let uu____3139 =
                                               let uu____3143 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____3143, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3139
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
                                             let uu____3156 =
                                               let uu____3160 =
                                                 let uu____3161 =
                                                   let uu____3167 =
                                                     let uu____3168 =
                                                       let uu____3171 =
                                                         let uu____3172 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3172
                                                          in
                                                       (f_has_t, uu____3171)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3168
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3167)
                                                    in
                                                 mkForall_fuel uu____3161  in
                                               (uu____3160,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3156
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____3185 =
                                               let uu____3189 =
                                                 let uu____3190 =
                                                   let uu____3196 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3196)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3190
                                                  in
                                               (uu____3189, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3185
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
                                           ((let uu____3210 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3210);
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
                     let uu____3221 =
                       let uu____3225 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____3225, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3221  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____3234 =
                       let uu____3238 =
                         let uu____3239 =
                           let uu____3245 =
                             let uu____3246 =
                               let uu____3249 =
                                 let uu____3250 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3250
                                  in
                               (f_has_t, uu____3249)  in
                             FStar_SMTEncoding_Util.mkImp uu____3246  in
                           ([[f_has_t]], [fsym], uu____3245)  in
                         mkForall_fuel uu____3239  in
                       (uu____3238, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3234  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3264 ->
           let uu____3269 =
             let uu____3272 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____3272 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3277;
                 FStar_Syntax_Syntax.pos = uu____3278;
                 FStar_Syntax_Syntax.vars = uu____3279;_} ->
                 let uu____3286 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____3286 with
                  | (b,f1) ->
                      let uu____3300 =
                        let uu____3301 = FStar_List.hd b  in fst uu____3301
                         in
                      (uu____3300, f1))
             | uu____3306 -> failwith "impossible"  in
           (match uu____3269 with
            | (x,f) ->
                let uu____3313 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____3313 with
                 | (base_t,decls) ->
                     let uu____3320 = gen_term_var env x  in
                     (match uu____3320 with
                      | (x1,xtm,env') ->
                          let uu____3329 = encode_formula f env'  in
                          (match uu____3329 with
                           | (refinement,decls') ->
                               let uu____3336 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____3336 with
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
                                      let uu____3347 =
                                        let uu____3349 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____3353 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____3349
                                          uu____3353
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3347
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3369  ->
                                              match uu____3369 with
                                              | (y,uu____3373) ->
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
                                    let uu____3392 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____3392 with
                                     | Some cache_entry ->
                                         let uu____3397 =
                                           let uu____3398 =
                                             let uu____3402 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3402)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3398
                                            in
                                         (uu____3397,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____3414 =
                                             let uu____3415 =
                                               let uu____3416 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3416
                                                in
                                             Prims.strcat module_name
                                               uu____3415
                                              in
                                           varops.mk_unique uu____3414  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____3425 =
                                             let uu____3429 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____3429)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3425
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
                                           let uu____3439 =
                                             let uu____3443 =
                                               let uu____3444 =
                                                 let uu____3450 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3450)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3444
                                                in
                                             (uu____3443,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3439
                                            in
                                         let t_kinding =
                                           let uu____3460 =
                                             let uu____3464 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____3464,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3460
                                            in
                                         let t_interp =
                                           let uu____3474 =
                                             let uu____3478 =
                                               let uu____3479 =
                                                 let uu____3485 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3485)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3479
                                                in
                                             let uu____3497 =
                                               let uu____3499 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____3499  in
                                             (uu____3478, uu____3497,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3474
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____3504 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3504);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3521 = FStar_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3521  in
           let uu____3525 = encode_term_pred None k env ttm  in
           (match uu____3525 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3533 =
                    let uu____3537 =
                      let uu____3538 =
                        let uu____3539 =
                          let uu____3540 = FStar_Unionfind.uvar_id uv  in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3540
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____3539  in
                      varops.mk_unique uu____3538  in
                    (t_has_k, (Some "Uvar typing"), uu____3537)  in
                  FStar_SMTEncoding_Util.mkAssume uu____3533  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3546 ->
           let uu____3556 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____3556 with
            | (head1,args_e) ->
                let uu____3584 =
                  let uu____3592 =
                    let uu____3593 = FStar_Syntax_Subst.compress head1  in
                    uu____3593.FStar_Syntax_Syntax.n  in
                  (uu____3592, args_e)  in
                (match uu____3584 with
                 | uu____3603 when head_redex env head1 ->
                     let uu____3611 = whnf env t  in
                     encode_term uu____3611 env
                 | uu____3612 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3625;
                       FStar_Syntax_Syntax.pos = uu____3626;
                       FStar_Syntax_Syntax.vars = uu____3627;_},uu____3628),uu____3629::
                    (v1,uu____3631)::(v2,uu____3633)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3671 = encode_term v1 env  in
                     (match uu____3671 with
                      | (v11,decls1) ->
                          let uu____3678 = encode_term v2 env  in
                          (match uu____3678 with
                           | (v21,decls2) ->
                               let uu____3685 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3685,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3688::(v1,uu____3690)::(v2,uu____3692)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3726 = encode_term v1 env  in
                     (match uu____3726 with
                      | (v11,decls1) ->
                          let uu____3733 = encode_term v2 env  in
                          (match uu____3733 with
                           | (v21,decls2) ->
                               let uu____3740 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____3740,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3742) ->
                     let e0 =
                       let uu____3754 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3754
                        in
                     ((let uu____3760 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____3760
                       then
                         let uu____3761 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3761
                       else ());
                      (let e =
                         let uu____3766 =
                           let uu____3767 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____3768 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3767
                             uu____3768
                            in
                         uu____3766 None t0.FStar_Syntax_Syntax.pos  in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3777),(arg,uu____3779)::[]) -> encode_term arg env
                 | uu____3797 ->
                     let uu____3805 = encode_args args_e env  in
                     (match uu____3805 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3838 = encode_term head1 env  in
                            match uu____3838 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3877 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____3877 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3919  ->
                                                 fun uu____3920  ->
                                                   match (uu____3919,
                                                           uu____3920)
                                                   with
                                                   | ((bv,uu____3934),
                                                      (a,uu____3936)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____3950 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____3950
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____3955 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____3955 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____3965 =
                                                   let uu____3969 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____3974 =
                                                     let uu____3975 =
                                                       let uu____3976 =
                                                         let uu____3977 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____3977
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3976
                                                        in
                                                     varops.mk_unique
                                                       uu____3975
                                                      in
                                                   (uu____3969,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3974)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3965
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____3994 = lookup_free_var_sym env fv  in
                            match uu____3994 with
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
                                   FStar_Syntax_Syntax.tk = uu____4017;
                                   FStar_Syntax_Syntax.pos = uu____4018;
                                   FStar_Syntax_Syntax.vars = uu____4019;_},uu____4020)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4031;
                                   FStar_Syntax_Syntax.pos = uu____4032;
                                   FStar_Syntax_Syntax.vars = uu____4033;_},uu____4034)
                                ->
                                let uu____4039 =
                                  let uu____4040 =
                                    let uu____4043 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____4043
                                      FStar_Pervasives.fst
                                     in
                                  FStar_All.pipe_right uu____4040
                                    FStar_Pervasives.snd
                                   in
                                Some uu____4039
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4063 =
                                  let uu____4064 =
                                    let uu____4067 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____4067
                                      FStar_Pervasives.fst
                                     in
                                  FStar_All.pipe_right uu____4064
                                    FStar_Pervasives.snd
                                   in
                                Some uu____4063
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4086,(FStar_Util.Inl t1,uu____4088),uu____4089)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4127,(FStar_Util.Inr c,uu____4129),uu____4130)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4168 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4188 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4188
                                  in
                               let uu____4189 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____4189 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4199;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4200;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4201;_},uu____4202)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____4226 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4271 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____4271 with
            | (bs1,body1,opening) ->
                let fallback uu____4286 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____4291 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____4291, [decl])  in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4302 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1  in
                      Prims.op_Negation uu____4302
                  | FStar_Util.Inr (eff,uu____4304) ->
                      let uu____4310 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff
                         in
                      FStar_All.pipe_right uu____4310 Prims.op_Negation
                   in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2  in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4355 = lc.FStar_Syntax_Syntax.comp ()  in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4356 = env1.tcenv  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4356.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4356.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4356.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4356.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4356.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4356.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4356.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4356.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4356.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4356.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4356.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4356.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4356.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4356.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4356.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4356.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4356.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4356.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4356.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4356.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4356.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4356.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4356.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4355 FStar_Syntax_Syntax.U_unknown
                           in
                        let uu____4357 =
                          let uu____4358 = FStar_Syntax_Syntax.mk_Total typ
                             in
                          FStar_Syntax_Util.lcomp_of_comp uu____4358  in
                        FStar_Util.Inl uu____4357
                    | FStar_Util.Inr (eff_name,uu____4365) -> c  in
                  (c1, reified_body)  in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4396 =
                        let uu____4397 = lc1.FStar_Syntax_Syntax.comp ()  in
                        FStar_Syntax_Subst.subst_comp opening uu____4397  in
                      FStar_All.pipe_right uu____4396
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4409 =
                        let uu____4410 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____4410 FStar_Pervasives.fst
                         in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4418 =
                          let uu____4419 = new_uvar1 ()  in
                          FStar_Syntax_Syntax.mk_Total uu____4419  in
                        FStar_All.pipe_right uu____4418
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4423 =
                             let uu____4424 = new_uvar1 ()  in
                             FStar_Syntax_Syntax.mk_GTotal uu____4424  in
                           FStar_All.pipe_right uu____4423
                             (fun _0_33  -> Some _0_33))
                        else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____4435 =
                         let uu____4436 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4436
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4435);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc  in
                     let uu____4451 =
                       (is_impure lc1) &&
                         (let uu____4452 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1
                             in
                          Prims.op_Negation uu____4452)
                        in
                     if uu____4451
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____4457 = encode_binders None bs1 env  in
                        match uu____4457 with
                        | (vars,guards,envbody,decls,uu____4472) ->
                            let uu____4479 =
                              let uu____4487 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1
                                 in
                              if uu____4487
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1)  in
                            (match uu____4479 with
                             | (lc2,body2) ->
                                 let uu____4512 = encode_term body2 envbody
                                    in
                                 (match uu____4512 with
                                  | (body3,decls') ->
                                      let uu____4519 =
                                        let uu____4524 = codomain_eff lc2  in
                                        match uu____4524 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c
                                               in
                                            let uu____4536 =
                                              encode_term tfun env  in
                                            (match uu____4536 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1))
                                         in
                                      (match uu____4519 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4555 =
                                               let uu____4561 =
                                                 let uu____4562 =
                                                   let uu____4565 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards
                                                      in
                                                   (uu____4565, body3)  in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4562
                                                  in
                                               ([], vars, uu____4561)  in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4555
                                              in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body
                                              in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4573 =
                                                   let uu____4575 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1
                                                      in
                                                   FStar_List.append
                                                     uu____4575 cvars
                                                    in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4573
                                              in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body)
                                              in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey
                                              in
                                           let uu____4586 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash
                                              in
                                           (match uu____4586 with
                                            | Some cache_entry ->
                                                let uu____4591 =
                                                  let uu____4592 =
                                                    let uu____4596 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4596)
                                                     in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4592
                                                   in
                                                (uu____4591,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4602 =
                                                  is_an_eta_expansion env
                                                    vars body3
                                                   in
                                                (match uu____4602 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4609 =
                                                         let uu____4610 =
                                                           FStar_Util.smap_size
                                                             env.cache
                                                            in
                                                         uu____4610 =
                                                           cache_size
                                                          in
                                                       if uu____4609
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'')
                                                        in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives.snd
                                                         cvars1
                                                        in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name
                                                          in
                                                       let fsym =
                                                         let uu____4621 =
                                                           let uu____4622 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash
                                                              in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4622
                                                            in
                                                         varops.mk_unique
                                                           uu____4621
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
                                                       let uu____4627 =
                                                         let uu____4631 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1
                                                            in
                                                         (fsym, uu____4631)
                                                          in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4627
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
                                                           let uu____4643 =
                                                             let uu____4644 =
                                                               let uu____4648
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t)
                                                                  in
                                                               (uu____4648,
                                                                 (Some a_name),
                                                                 a_name)
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4644
                                                              in
                                                           [uu____4643]
                                                        in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym
                                                          in
                                                       let uu____4656 =
                                                         let uu____4660 =
                                                           let uu____4661 =
                                                             let uu____4667 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3)
                                                                in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4667)
                                                              in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4661
                                                            in
                                                         (uu____4660,
                                                           (Some a_name),
                                                           a_name)
                                                          in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4656
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
                                                     ((let uu____4677 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls
                                                          in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4677);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4679,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4680;
                          FStar_Syntax_Syntax.lbunivs = uu____4681;
                          FStar_Syntax_Syntax.lbtyp = uu____4682;
                          FStar_Syntax_Syntax.lbeff = uu____4683;
                          FStar_Syntax_Syntax.lbdef = uu____4684;_}::uu____4685),uu____4686)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4704;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4706;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4722 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____4735 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____4735, [decl_e])))
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
              let uu____4777 = encode_term e1 env  in
              match uu____4777 with
              | (ee1,decls1) ->
                  let uu____4784 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____4784 with
                   | (xs,e21) ->
                       let uu____4798 = FStar_List.hd xs  in
                       (match uu____4798 with
                        | (x1,uu____4806) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____4808 = encode_body e21 env'  in
                            (match uu____4808 with
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
            let uu____4830 =
              let uu____4834 =
                let uu____4835 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____4835  in
              gen_term_var env uu____4834  in
            match uu____4830 with
            | (scrsym,scr',env1) ->
                let uu____4845 = encode_term e env1  in
                (match uu____4845 with
                 | (scr,decls) ->
                     let uu____4852 =
                       let encode_branch b uu____4868 =
                         match uu____4868 with
                         | (else_case,decls1) ->
                             let uu____4879 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____4879 with
                              | (p,w,br) ->
                                  let uu____4900 = encode_pat env1 p  in
                                  (match uu____4900 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4920  ->
                                                   match uu____4920 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____4925 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4940 =
                                               encode_term w1 env2  in
                                             (match uu____4940 with
                                              | (w2,decls2) ->
                                                  let uu____4948 =
                                                    let uu____4949 =
                                                      let uu____4952 =
                                                        let uu____4953 =
                                                          let uu____4956 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____4956)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4953
                                                         in
                                                      (guard, uu____4952)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4949
                                                     in
                                                  (uu____4948, decls2))
                                          in
                                       (match uu____4925 with
                                        | (guard1,decls2) ->
                                            let uu____4964 =
                                              encode_br br env2  in
                                            (match uu____4964 with
                                             | (br1,decls3) ->
                                                 let uu____4972 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____4972,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____4852 with
                      | (match_tm,decls1) ->
                          let uu____4983 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____4983, decls1)))

and encode_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5005 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____5005
       then
         let uu____5006 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5006
       else ());
      (let uu____5008 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____5008 with
       | (vars,pat_term) ->
           let uu____5018 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5041  ->
                     fun v1  ->
                       match uu____5041 with
                       | (env1,vars1) ->
                           let uu____5069 = gen_term_var env1 v1  in
                           (match uu____5069 with
                            | (xx,uu____5081,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____5018 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5128 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5129 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5130 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5136 =
                        let uu____5139 = encode_const c  in
                        (scrutinee, uu____5139)  in
                      FStar_SMTEncoding_Util.mkEq uu____5136
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____5158 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____5158 with
                        | (uu____5162,uu____5163::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5165 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5186  ->
                                  match uu____5186 with
                                  | (arg,uu____5192) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5202 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____5202))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5222) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5241 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5256 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5278  ->
                                  match uu____5278 with
                                  | (arg,uu____5287) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5297 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____5297))
                         in
                      FStar_All.pipe_right uu____5256 FStar_List.flatten
                   in
                let pat_term1 uu____5313 = encode_term pat_term env1  in
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
      let uu____5320 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5335  ->
                fun uu____5336  ->
                  match (uu____5335, uu____5336) with
                  | ((tms,decls),(t,uu____5356)) ->
                      let uu____5367 = encode_term t env  in
                      (match uu____5367 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5320 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5401 = FStar_Syntax_Util.list_elements e  in
        match uu____5401 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             [])
         in
      let one_pat p =
        let uu____5419 =
          let uu____5429 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____5429 FStar_Syntax_Util.head_and_args  in
        match uu____5419 with
        | (head1,args) ->
            let uu____5460 =
              let uu____5468 =
                let uu____5469 = FStar_Syntax_Util.un_uinst head1  in
                uu____5469.FStar_Syntax_Syntax.n  in
              (uu____5468, args)  in
            (match uu____5460 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5483,uu____5484)::(e,uu____5486)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5517)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5538 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or t1 =
          let uu____5571 =
            let uu____5581 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____5581 FStar_Syntax_Util.head_and_args
             in
          match uu____5571 with
          | (head1,args) ->
              let uu____5610 =
                let uu____5618 =
                  let uu____5619 = FStar_Syntax_Util.un_uinst head1  in
                  uu____5619.FStar_Syntax_Syntax.n  in
                (uu____5618, args)  in
              (match uu____5610 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5632)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5652 -> None)
           in
        match elts with
        | t1::[] ->
            let uu____5670 = smt_pat_or t1  in
            (match uu____5670 with
             | Some e ->
                 let uu____5686 = list_elements1 e  in
                 FStar_All.pipe_right uu____5686
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5703 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____5703
                           (FStar_List.map one_pat)))
             | uu____5717 ->
                 let uu____5721 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____5721])
        | uu____5752 ->
            let uu____5754 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____5754]
         in
      let uu____5785 =
        let uu____5801 =
          let uu____5802 = FStar_Syntax_Subst.compress t  in
          uu____5802.FStar_Syntax_Syntax.n  in
        match uu____5801 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5832 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____5832 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5867;
                        FStar_Syntax_Syntax.effect_name = uu____5868;
                        FStar_Syntax_Syntax.result_typ = uu____5869;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5871)::(post,uu____5873)::(pats,uu____5875)::[];
                        FStar_Syntax_Syntax.flags = uu____5876;_}
                      ->
                      let uu____5908 = lemma_pats pats  in
                      (binders1, pre, post, uu____5908)
                  | uu____5927 -> failwith "impos"))
        | uu____5943 -> failwith "Impos"  in
      match uu____5785 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5988 = env  in
            {
              bindings = (uu___137_5988.bindings);
              depth = (uu___137_5988.depth);
              tcenv = (uu___137_5988.tcenv);
              warn = (uu___137_5988.warn);
              cache = (uu___137_5988.cache);
              nolabels = (uu___137_5988.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5988.encode_non_total_function_typ);
              current_module_name = (uu___137_5988.current_module_name)
            }  in
          let uu____5989 = encode_binders None binders env1  in
          (match uu____5989 with
           | (vars,guards,env2,decls,uu____6004) ->
               let uu____6011 =
                 let uu____6018 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6049 =
                             let uu____6054 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6070  ->
                                       match uu____6070 with
                                       | (t1,uu____6077) ->
                                           encode_term t1 env2))
                                in
                             FStar_All.pipe_right uu____6054 FStar_List.unzip
                              in
                           match uu____6049 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____6018 FStar_List.unzip  in
               (match uu____6011 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let env3 =
                      let uu___138_6127 = env2  in
                      {
                        bindings = (uu___138_6127.bindings);
                        depth = (uu___138_6127.depth);
                        tcenv = (uu___138_6127.tcenv);
                        warn = (uu___138_6127.warn);
                        cache = (uu___138_6127.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6127.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6127.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6127.current_module_name)
                      }  in
                    let uu____6128 =
                      let uu____6131 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____6131 env3  in
                    (match uu____6128 with
                     | (pre1,decls'') ->
                         let uu____6136 =
                           let uu____6139 = FStar_Syntax_Util.unmeta post  in
                           encode_formula uu____6139 env3  in
                         (match uu____6136 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____6146 =
                                let uu____6147 =
                                  let uu____6153 =
                                    let uu____6154 =
                                      let uu____6157 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____6157, post1)  in
                                    FStar_SMTEncoding_Util.mkImp uu____6154
                                     in
                                  (pats, vars, uu____6153)  in
                                FStar_SMTEncoding_Util.mkForall uu____6147
                                 in
                              (uu____6146, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6170 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____6170
        then
          let uu____6171 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____6172 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6171 uu____6172
        else ()  in
      let enc f r l =
        let uu____6199 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6212 = encode_term (fst x) env  in
                 match uu____6212 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____6199 with
        | (decls,args) ->
            let uu____6229 =
              let uu___139_6230 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6230.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6230.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6229, decls)
         in
      let const_op f r uu____6249 = let uu____6252 = f r  in (uu____6252, [])
         in
      let un_op f l =
        let uu____6268 = FStar_List.hd l  in FStar_All.pipe_left f uu____6268
         in
      let bin_op f uu___111_6281 =
        match uu___111_6281 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6289 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6316 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6325  ->
                 match uu____6325 with
                 | (t,uu____6333) ->
                     let uu____6334 = encode_formula t env  in
                     (match uu____6334 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6316 with
        | (decls,phis) ->
            let uu____6351 =
              let uu___140_6352 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6352.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6352.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6351, decls)
         in
      let eq_op r uu___112_6368 =
        match uu___112_6368 with
        | uu____6371::e1::e2::[] ->
            let uu____6402 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6402 r [e1; e2]
        | uu____6421::uu____6422::e1::e2::[] ->
            let uu____6461 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6461 r [e1; e2]
        | l ->
            let uu____6481 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
            uu____6481 r l
         in
      let mk_imp1 r uu___113_6500 =
        match uu___113_6500 with
        | (lhs,uu____6504)::(rhs,uu____6506)::[] ->
            let uu____6527 = encode_formula rhs env  in
            (match uu____6527 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6536) ->
                      (l1, decls1)
                  | uu____6539 ->
                      let uu____6540 = encode_formula lhs env  in
                      (match uu____6540 with
                       | (l2,decls2) ->
                           let uu____6547 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6547, (FStar_List.append decls1 decls2)))))
        | uu____6549 -> failwith "impossible"  in
      let mk_ite r uu___114_6564 =
        match uu___114_6564 with
        | (guard,uu____6568)::(_then,uu____6570)::(_else,uu____6572)::[] ->
            let uu____6601 = encode_formula guard env  in
            (match uu____6601 with
             | (g,decls1) ->
                 let uu____6608 = encode_formula _then env  in
                 (match uu____6608 with
                  | (t,decls2) ->
                      let uu____6615 = encode_formula _else env  in
                      (match uu____6615 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6624 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____6643 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____6643  in
      let connectives =
        let uu____6655 =
          let uu____6664 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____6664)  in
        let uu____6677 =
          let uu____6687 =
            let uu____6696 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____6696)  in
          let uu____6709 =
            let uu____6719 =
              let uu____6729 =
                let uu____6738 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____6738)  in
              let uu____6751 =
                let uu____6761 =
                  let uu____6771 =
                    let uu____6780 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____6780)  in
                  [uu____6771;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6761  in
              uu____6729 :: uu____6751  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6719  in
          uu____6687 :: uu____6709  in
        uu____6655 :: uu____6677  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6942 = encode_formula phi' env  in
            (match uu____6942 with
             | (phi2,decls) ->
                 let uu____6949 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____6949, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6950 ->
            let uu____6955 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____6955 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6984 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____6984 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6992;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6994;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7010 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____7010 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7042::(x,uu____7044)::(t,uu____7046)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7080 = encode_term x env  in
                 (match uu____7080 with
                  | (x1,decls) ->
                      let uu____7087 = encode_term t env  in
                      (match uu____7087 with
                       | (t1,decls') ->
                           let uu____7094 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____7094, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7098)::(msg,uu____7100)::(phi2,uu____7102)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7136 =
                   let uu____7139 =
                     let uu____7140 = FStar_Syntax_Subst.compress r  in
                     uu____7140.FStar_Syntax_Syntax.n  in
                   let uu____7143 =
                     let uu____7144 = FStar_Syntax_Subst.compress msg  in
                     uu____7144.FStar_Syntax_Syntax.n  in
                   (uu____7139, uu____7143)  in
                 (match uu____7136 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7151))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____7167 -> fallback phi2)
             | uu____7170 when head_redex env head2 ->
                 let uu____7178 = whnf env phi1  in
                 encode_formula uu____7178 env
             | uu____7179 ->
                 let uu____7187 = encode_term phi1 env  in
                 (match uu____7187 with
                  | (tt,decls) ->
                      let uu____7194 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7195 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7195.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7195.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____7194, decls)))
        | uu____7198 ->
            let uu____7199 = encode_term phi1 env  in
            (match uu____7199 with
             | (tt,decls) ->
                 let uu____7206 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7207 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7207.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7207.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____7206, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____7234 = encode_binders None bs env1  in
        match uu____7234 with
        | (vars,guards,env2,decls,uu____7256) ->
            let uu____7263 =
              let uu____7270 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7293 =
                          let uu____7298 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7312  ->
                                    match uu____7312 with
                                    | (t,uu____7318) ->
                                        encode_term t
                                          (let uu___143_7319 = env2  in
                                           {
                                             bindings =
                                               (uu___143_7319.bindings);
                                             depth = (uu___143_7319.depth);
                                             tcenv = (uu___143_7319.tcenv);
                                             warn = (uu___143_7319.warn);
                                             cache = (uu___143_7319.cache);
                                             nolabels =
                                               (uu___143_7319.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7319.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7319.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____7298 FStar_List.unzip
                           in
                        match uu____7293 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7270 FStar_List.unzip  in
            (match uu____7263 with
             | (pats,decls') ->
                 let uu____7371 = encode_formula body env2  in
                 (match uu____7371 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7390;
                             FStar_SMTEncoding_Term.rng = uu____7391;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7399 -> guards  in
                      let uu____7402 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7402, body1,
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
                (fun uu____7436  ->
                   match uu____7436 with
                   | (x,uu____7440) ->
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
               let uu____7446 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7452 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7452) uu____7446 tl1
                in
             let uu____7454 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7466  ->
                       match uu____7466 with
                       | (b,uu____7470) ->
                           let uu____7471 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7471))
                in
             (match uu____7454 with
              | None  -> ()
              | Some (x,uu____7475) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7485 =
                    let uu____7486 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7486
                     in
                  FStar_Errors.warn pos uu____7485)
          in
       let uu____7487 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7487 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7493 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7529  ->
                     match uu____7529 with
                     | (l,uu____7539) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7493 with
            | None  -> fallback phi1
            | Some (uu____7562,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7591 = encode_q_body env vars pats body  in
             match uu____7591 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7617 =
                     let uu____7623 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____7623)  in
                   FStar_SMTEncoding_Term.mkForall uu____7617
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7635 = encode_q_body env vars pats body  in
             match uu____7635 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7660 =
                   let uu____7661 =
                     let uu____7667 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____7667)  in
                   FStar_SMTEncoding_Term.mkExists uu____7661
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____7660, decls))))

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
  let uu____7721 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____7721 with
  | (asym,a) ->
      let uu____7726 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____7726 with
       | (xsym,x) ->
           let uu____7731 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____7731 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7761 =
                      let uu____7767 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd)
                         in
                      (x1, uu____7767, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____7761  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____7782 =
                      let uu____7786 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____7786)  in
                    FStar_SMTEncoding_Util.mkApp uu____7782  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____7794 =
                    let uu____7796 =
                      let uu____7798 =
                        let uu____7800 =
                          let uu____7801 =
                            let uu____7805 =
                              let uu____7806 =
                                let uu____7812 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____7812)  in
                              FStar_SMTEncoding_Util.mkForall uu____7806  in
                            (uu____7805, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____7801  in
                        let uu____7821 =
                          let uu____7823 =
                            let uu____7824 =
                              let uu____7828 =
                                let uu____7829 =
                                  let uu____7835 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____7835)  in
                                FStar_SMTEncoding_Util.mkForall uu____7829
                                 in
                              (uu____7828,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____7824  in
                          [uu____7823]  in
                        uu____7800 :: uu____7821  in
                      xtok_decl :: uu____7798  in
                    xname_decl :: uu____7796  in
                  (xtok1, uu____7794)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____7884 =
                    let uu____7892 =
                      let uu____7898 =
                        let uu____7899 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7899
                         in
                      quant axy uu____7898  in
                    (FStar_Syntax_Const.op_Eq, uu____7892)  in
                  let uu____7905 =
                    let uu____7914 =
                      let uu____7922 =
                        let uu____7928 =
                          let uu____7929 =
                            let uu____7930 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____7930  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7929
                           in
                        quant axy uu____7928  in
                      (FStar_Syntax_Const.op_notEq, uu____7922)  in
                    let uu____7936 =
                      let uu____7945 =
                        let uu____7953 =
                          let uu____7959 =
                            let uu____7960 =
                              let uu____7961 =
                                let uu____7964 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____7965 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____7964, uu____7965)  in
                              FStar_SMTEncoding_Util.mkLT uu____7961  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7960
                             in
                          quant xy uu____7959  in
                        (FStar_Syntax_Const.op_LT, uu____7953)  in
                      let uu____7971 =
                        let uu____7980 =
                          let uu____7988 =
                            let uu____7994 =
                              let uu____7995 =
                                let uu____7996 =
                                  let uu____7999 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____8000 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____7999, uu____8000)  in
                                FStar_SMTEncoding_Util.mkLTE uu____7996  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7995
                               in
                            quant xy uu____7994  in
                          (FStar_Syntax_Const.op_LTE, uu____7988)  in
                        let uu____8006 =
                          let uu____8015 =
                            let uu____8023 =
                              let uu____8029 =
                                let uu____8030 =
                                  let uu____8031 =
                                    let uu____8034 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____8035 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____8034, uu____8035)  in
                                  FStar_SMTEncoding_Util.mkGT uu____8031  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8030
                                 in
                              quant xy uu____8029  in
                            (FStar_Syntax_Const.op_GT, uu____8023)  in
                          let uu____8041 =
                            let uu____8050 =
                              let uu____8058 =
                                let uu____8064 =
                                  let uu____8065 =
                                    let uu____8066 =
                                      let uu____8069 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____8070 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____8069, uu____8070)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____8066
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8065
                                   in
                                quant xy uu____8064  in
                              (FStar_Syntax_Const.op_GTE, uu____8058)  in
                            let uu____8076 =
                              let uu____8085 =
                                let uu____8093 =
                                  let uu____8099 =
                                    let uu____8100 =
                                      let uu____8101 =
                                        let uu____8104 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____8105 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____8104, uu____8105)  in
                                      FStar_SMTEncoding_Util.mkSub uu____8101
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8100
                                     in
                                  quant xy uu____8099  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8093)
                                 in
                              let uu____8111 =
                                let uu____8120 =
                                  let uu____8128 =
                                    let uu____8134 =
                                      let uu____8135 =
                                        let uu____8136 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8136
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8135
                                       in
                                    quant qx uu____8134  in
                                  (FStar_Syntax_Const.op_Minus, uu____8128)
                                   in
                                let uu____8142 =
                                  let uu____8151 =
                                    let uu____8159 =
                                      let uu____8165 =
                                        let uu____8166 =
                                          let uu____8167 =
                                            let uu____8170 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____8171 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____8170, uu____8171)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8167
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8166
                                         in
                                      quant xy uu____8165  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8159)
                                     in
                                  let uu____8177 =
                                    let uu____8186 =
                                      let uu____8194 =
                                        let uu____8200 =
                                          let uu____8201 =
                                            let uu____8202 =
                                              let uu____8205 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____8206 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____8205, uu____8206)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8202
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8201
                                           in
                                        quant xy uu____8200  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8194)
                                       in
                                    let uu____8212 =
                                      let uu____8221 =
                                        let uu____8229 =
                                          let uu____8235 =
                                            let uu____8236 =
                                              let uu____8237 =
                                                let uu____8240 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____8241 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____8240, uu____8241)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8237
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8236
                                             in
                                          quant xy uu____8235  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8229)
                                         in
                                      let uu____8247 =
                                        let uu____8256 =
                                          let uu____8264 =
                                            let uu____8270 =
                                              let uu____8271 =
                                                let uu____8272 =
                                                  let uu____8275 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8276 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8275, uu____8276)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8272
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8271
                                               in
                                            quant xy uu____8270  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8264)
                                           in
                                        let uu____8282 =
                                          let uu____8291 =
                                            let uu____8299 =
                                              let uu____8305 =
                                                let uu____8306 =
                                                  let uu____8307 =
                                                    let uu____8310 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8311 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8310, uu____8311)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8307
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8306
                                                 in
                                              quant xy uu____8305  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8299)
                                             in
                                          let uu____8317 =
                                            let uu____8326 =
                                              let uu____8334 =
                                                let uu____8340 =
                                                  let uu____8341 =
                                                    let uu____8342 =
                                                      let uu____8345 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8346 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8345,
                                                        uu____8346)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8342
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8341
                                                   in
                                                quant xy uu____8340  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8334)
                                               in
                                            let uu____8352 =
                                              let uu____8361 =
                                                let uu____8369 =
                                                  let uu____8375 =
                                                    let uu____8376 =
                                                      let uu____8377 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8377
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8376
                                                     in
                                                  quant qx uu____8375  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8369)
                                                 in
                                              [uu____8361]  in
                                            uu____8326 :: uu____8352  in
                                          uu____8291 :: uu____8317  in
                                        uu____8256 :: uu____8282  in
                                      uu____8221 :: uu____8247  in
                                    uu____8186 :: uu____8212  in
                                  uu____8151 :: uu____8177  in
                                uu____8120 :: uu____8142  in
                              uu____8085 :: uu____8111  in
                            uu____8050 :: uu____8076  in
                          uu____8015 :: uu____8041  in
                        uu____7980 :: uu____8006  in
                      uu____7945 :: uu____7971  in
                    uu____7914 :: uu____7936  in
                  uu____7884 :: uu____7905  in
                let mk1 l v1 =
                  let uu____8505 =
                    let uu____8510 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8542  ->
                              match uu____8542 with
                              | (l',uu____8551) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8510
                      (FStar_Option.map
                         (fun uu____8584  ->
                            match uu____8584 with | (uu____8595,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8505 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8636  ->
                          match uu____8636 with
                          | (l',uu____8645) -> FStar_Ident.lid_equals l l'))
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
        let uu____8671 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____8671 with
        | (xxsym,xx) ->
            let uu____8676 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____8676 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____8684 =
                   let uu____8688 =
                     let uu____8689 =
                       let uu____8695 =
                         let uu____8696 =
                           let uu____8699 =
                             let uu____8700 =
                               let uu____8703 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____8703)  in
                             FStar_SMTEncoding_Util.mkEq uu____8700  in
                           (xx_has_type, uu____8699)  in
                         FStar_SMTEncoding_Util.mkImp uu____8696  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8695)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____8689  in
                   let uu____8716 =
                     let uu____8717 =
                       let uu____8718 =
                         let uu____8719 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____8719  in
                       Prims.strcat module_name uu____8718  in
                     varops.mk_unique uu____8717  in
                   (uu____8688, (Some "pretyping"), uu____8716)  in
                 FStar_SMTEncoding_Util.mkAssume uu____8684)
  
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
    let uu____8749 =
      let uu____8750 =
        let uu____8754 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____8754, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____8750  in
    let uu____8756 =
      let uu____8758 =
        let uu____8759 =
          let uu____8763 =
            let uu____8764 =
              let uu____8770 =
                let uu____8771 =
                  let uu____8774 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____8774)  in
                FStar_SMTEncoding_Util.mkImp uu____8771  in
              ([[typing_pred]], [xx], uu____8770)  in
            mkForall_fuel uu____8764  in
          (uu____8763, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____8759  in
      [uu____8758]  in
    uu____8749 :: uu____8756  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____8802 =
      let uu____8803 =
        let uu____8807 =
          let uu____8808 =
            let uu____8814 =
              let uu____8817 =
                let uu____8819 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____8819]  in
              [uu____8817]  in
            let uu____8822 =
              let uu____8823 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8823 tt  in
            (uu____8814, [bb], uu____8822)  in
          FStar_SMTEncoding_Util.mkForall uu____8808  in
        (uu____8807, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____8803  in
    let uu____8834 =
      let uu____8836 =
        let uu____8837 =
          let uu____8841 =
            let uu____8842 =
              let uu____8848 =
                let uu____8849 =
                  let uu____8852 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____8852)  in
                FStar_SMTEncoding_Util.mkImp uu____8849  in
              ([[typing_pred]], [xx], uu____8848)  in
            mkForall_fuel uu____8842  in
          (uu____8841, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____8837  in
      [uu____8836]  in
    uu____8802 :: uu____8834  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____8886 =
        let uu____8887 =
          let uu____8891 =
            let uu____8893 =
              let uu____8895 =
                let uu____8897 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____8898 =
                  let uu____8900 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____8900]  in
                uu____8897 :: uu____8898  in
              tt :: uu____8895  in
            tt :: uu____8893  in
          ("Prims.Precedes", uu____8891)  in
        FStar_SMTEncoding_Util.mkApp uu____8887  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8886  in
    let precedes_y_x =
      let uu____8903 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8903  in
    let uu____8905 =
      let uu____8906 =
        let uu____8910 =
          let uu____8911 =
            let uu____8917 =
              let uu____8920 =
                let uu____8922 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____8922]  in
              [uu____8920]  in
            let uu____8925 =
              let uu____8926 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____8926 tt  in
            (uu____8917, [bb], uu____8925)  in
          FStar_SMTEncoding_Util.mkForall uu____8911  in
        (uu____8910, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____8906  in
    let uu____8937 =
      let uu____8939 =
        let uu____8940 =
          let uu____8944 =
            let uu____8945 =
              let uu____8951 =
                let uu____8952 =
                  let uu____8955 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____8955)  in
                FStar_SMTEncoding_Util.mkImp uu____8952  in
              ([[typing_pred]], [xx], uu____8951)  in
            mkForall_fuel uu____8945  in
          (uu____8944, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____8940  in
      let uu____8968 =
        let uu____8970 =
          let uu____8971 =
            let uu____8975 =
              let uu____8976 =
                let uu____8982 =
                  let uu____8983 =
                    let uu____8986 =
                      let uu____8987 =
                        let uu____8989 =
                          let uu____8991 =
                            let uu____8993 =
                              let uu____8994 =
                                let uu____8997 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8998 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____8997, uu____8998)  in
                              FStar_SMTEncoding_Util.mkGT uu____8994  in
                            let uu____8999 =
                              let uu____9001 =
                                let uu____9002 =
                                  let uu____9005 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____9006 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____9005, uu____9006)  in
                                FStar_SMTEncoding_Util.mkGTE uu____9002  in
                              let uu____9007 =
                                let uu____9009 =
                                  let uu____9010 =
                                    let uu____9013 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____9014 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____9013, uu____9014)  in
                                  FStar_SMTEncoding_Util.mkLT uu____9010  in
                                [uu____9009]  in
                              uu____9001 :: uu____9007  in
                            uu____8993 :: uu____8999  in
                          typing_pred_y :: uu____8991  in
                        typing_pred :: uu____8989  in
                      FStar_SMTEncoding_Util.mk_and_l uu____8987  in
                    (uu____8986, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____8983  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8982)
                 in
              mkForall_fuel uu____8976  in
            (uu____8975, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____8971  in
        [uu____8970]  in
      uu____8939 :: uu____8968  in
    uu____8905 :: uu____8937  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____9044 =
      let uu____9045 =
        let uu____9049 =
          let uu____9050 =
            let uu____9056 =
              let uu____9059 =
                let uu____9061 = FStar_SMTEncoding_Term.boxString b  in
                [uu____9061]  in
              [uu____9059]  in
            let uu____9064 =
              let uu____9065 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____9065 tt  in
            (uu____9056, [bb], uu____9064)  in
          FStar_SMTEncoding_Util.mkForall uu____9050  in
        (uu____9049, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____9045  in
    let uu____9076 =
      let uu____9078 =
        let uu____9079 =
          let uu____9083 =
            let uu____9084 =
              let uu____9090 =
                let uu____9091 =
                  let uu____9094 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____9094)  in
                FStar_SMTEncoding_Util.mkImp uu____9091  in
              ([[typing_pred]], [xx], uu____9090)  in
            mkForall_fuel uu____9084  in
          (uu____9083, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____9079  in
      [uu____9078]  in
    uu____9044 :: uu____9076  in
  let mk_ref1 env reft_name uu____9116 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____9127 =
        let uu____9131 =
          let uu____9133 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____9133]
           in
        (reft_name, uu____9131)  in
      FStar_SMTEncoding_Util.mkApp uu____9127  in
    let refb =
      let uu____9136 =
        let uu____9140 =
          let uu____9142 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____9142]
           in
        (reft_name, uu____9140)  in
      FStar_SMTEncoding_Util.mkApp uu____9136  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____9146 =
      let uu____9147 =
        let uu____9151 =
          let uu____9152 =
            let uu____9158 =
              let uu____9159 =
                let uu____9162 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____9162)  in
              FStar_SMTEncoding_Util.mkImp uu____9159  in
            ([[typing_pred]], [xx; aa], uu____9158)  in
          mkForall_fuel uu____9152  in
        (uu____9151, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Util.mkAssume uu____9147  in
    [uu____9146]  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____9202 =
      let uu____9203 =
        let uu____9207 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9207, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9203  in
    [uu____9202]  in
  let mk_and_interp env conj uu____9218 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9235 =
      let uu____9236 =
        let uu____9240 =
          let uu____9241 =
            let uu____9247 =
              let uu____9248 =
                let uu____9251 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9251, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9248  in
            ([[l_and_a_b]], [aa; bb], uu____9247)  in
          FStar_SMTEncoding_Util.mkForall uu____9241  in
        (uu____9240, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9236  in
    [uu____9235]  in
  let mk_or_interp env disj uu____9275 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9292 =
      let uu____9293 =
        let uu____9297 =
          let uu____9298 =
            let uu____9304 =
              let uu____9305 =
                let uu____9308 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9308, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9305  in
            ([[l_or_a_b]], [aa; bb], uu____9304)  in
          FStar_SMTEncoding_Util.mkForall uu____9298  in
        (uu____9297, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9293  in
    [uu____9292]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____9349 =
      let uu____9350 =
        let uu____9354 =
          let uu____9355 =
            let uu____9361 =
              let uu____9362 =
                let uu____9365 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9365, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9362  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9361)  in
          FStar_SMTEncoding_Util.mkForall uu____9355  in
        (uu____9354, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9350  in
    [uu____9349]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____9412 =
      let uu____9413 =
        let uu____9417 =
          let uu____9418 =
            let uu____9424 =
              let uu____9425 =
                let uu____9428 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9428, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9425  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9424)  in
          FStar_SMTEncoding_Util.mkForall uu____9418  in
        (uu____9417, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9413  in
    [uu____9412]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9473 =
      let uu____9474 =
        let uu____9478 =
          let uu____9479 =
            let uu____9485 =
              let uu____9486 =
                let uu____9489 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9489, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9486  in
            ([[l_imp_a_b]], [aa; bb], uu____9485)  in
          FStar_SMTEncoding_Util.mkForall uu____9479  in
        (uu____9478, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9474  in
    [uu____9473]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9530 =
      let uu____9531 =
        let uu____9535 =
          let uu____9536 =
            let uu____9542 =
              let uu____9543 =
                let uu____9546 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____9546, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9543  in
            ([[l_iff_a_b]], [aa; bb], uu____9542)  in
          FStar_SMTEncoding_Util.mkForall uu____9536  in
        (uu____9535, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9531  in
    [uu____9530]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____9580 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9580  in
    let uu____9582 =
      let uu____9583 =
        let uu____9587 =
          let uu____9588 =
            let uu____9594 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____9594)  in
          FStar_SMTEncoding_Util.mkForall uu____9588  in
        (uu____9587, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9583  in
    [uu____9582]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____9634 =
        let uu____9638 =
          let uu____9640 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9640]  in
        ("Valid", uu____9638)  in
      FStar_SMTEncoding_Util.mkApp uu____9634  in
    let uu____9642 =
      let uu____9643 =
        let uu____9647 =
          let uu____9648 =
            let uu____9654 =
              let uu____9655 =
                let uu____9658 =
                  let uu____9659 =
                    let uu____9665 =
                      let uu____9668 =
                        let uu____9670 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9670]  in
                      [uu____9668]  in
                    let uu____9673 =
                      let uu____9674 =
                        let uu____9677 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9677, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9674  in
                    (uu____9665, [xx1], uu____9673)  in
                  FStar_SMTEncoding_Util.mkForall uu____9659  in
                (uu____9658, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9655  in
            ([[l_forall_a_b]], [aa; bb], uu____9654)  in
          FStar_SMTEncoding_Util.mkForall uu____9648  in
        (uu____9647, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9643  in
    [uu____9642]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____9728 =
        let uu____9732 =
          let uu____9734 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____9734]  in
        ("Valid", uu____9732)  in
      FStar_SMTEncoding_Util.mkApp uu____9728  in
    let uu____9736 =
      let uu____9737 =
        let uu____9741 =
          let uu____9742 =
            let uu____9748 =
              let uu____9749 =
                let uu____9752 =
                  let uu____9753 =
                    let uu____9759 =
                      let uu____9762 =
                        let uu____9764 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____9764]  in
                      [uu____9762]  in
                    let uu____9767 =
                      let uu____9768 =
                        let uu____9771 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____9771, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____9768  in
                    (uu____9759, [xx1], uu____9767)  in
                  FStar_SMTEncoding_Util.mkExists uu____9753  in
                (uu____9752, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9749  in
            ([[l_exists_a_b]], [aa; bb], uu____9748)  in
          FStar_SMTEncoding_Util.mkForall uu____9742  in
        (uu____9741, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9737  in
    [uu____9736]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____9807 =
      let uu____9808 =
        let uu____9812 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____9813 = varops.mk_unique "typing_range_const"  in
        (uu____9812, (Some "Range_const typing"), uu____9813)  in
      FStar_SMTEncoding_Util.mkAssume uu____9808  in
    [uu____9807]  in
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
          let uu____10075 =
            FStar_Util.find_opt
              (fun uu____10093  ->
                 match uu____10093 with
                 | (l,uu____10103) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____10075 with
          | None  -> []
          | Some (uu____10125,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____10162 = encode_function_type_as_formula t env  in
        match uu____10162 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
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
            let uu____10194 =
              (let uu____10195 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10195) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10194
            then
              let uu____10199 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10199 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10211 =
                      let uu____10212 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10212.FStar_Syntax_Syntax.n  in
                    match uu____10211 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10217) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10234  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10237 -> []  in
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
              (let uu____10246 = prims.is lid  in
               if uu____10246
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10251 = prims.mk lid vname  in
                 match uu____10251 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10266 =
                    let uu____10272 = curried_arrow_formals_comp t_norm  in
                    match uu____10272 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10283 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10283
                          then
                            let uu____10284 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10285 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10285.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10285.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10285.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10285.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10285.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10285.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10285.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10285.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10285.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10285.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10285.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10285.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10285.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10285.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10285.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10285.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10285.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10285.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10285.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10285.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10285.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10285.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10285.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10284
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10292 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10292)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10266 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10319 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10319 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10332 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10356  ->
                                     match uu___115_10356 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10359 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10359 with
                                          | (uu____10370,(xxsym,uu____10372))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10382 =
                                                let uu____10383 =
                                                  let uu____10387 =
                                                    let uu____10388 =
                                                      let uu____10394 =
                                                        let uu____10395 =
                                                          let uu____10398 =
                                                            let uu____10399 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10399
                                                             in
                                                          (vapp, uu____10398)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10395
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10394)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10388
                                                     in
                                                  (uu____10387,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10383
                                                 in
                                              [uu____10382])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10410 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10410 with
                                          | (uu____10421,(xxsym,uu____10423))
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
                                              let uu____10437 =
                                                let uu____10438 =
                                                  let uu____10442 =
                                                    let uu____10443 =
                                                      let uu____10449 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10449)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10443
                                                     in
                                                  (uu____10442,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10438
                                                 in
                                              [uu____10437])
                                     | uu____10458 -> []))
                              in
                           let uu____10459 = encode_binders None formals env1
                              in
                           (match uu____10459 with
                            | (vars,guards,env',decls1,uu____10475) ->
                                let uu____10482 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10487 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10487, decls1)
                                  | Some p ->
                                      let uu____10489 = encode_formula p env'
                                         in
                                      (match uu____10489 with
                                       | (g,ds) ->
                                           let uu____10496 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10496,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10482 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10505 =
                                         let uu____10509 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10509)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10505
                                        in
                                     let uu____10514 =
                                       let vname_decl =
                                         let uu____10519 =
                                           let uu____10525 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10530  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____10525,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10519
                                          in
                                       let uu____10535 =
                                         let env2 =
                                           let uu___145_10539 = env1  in
                                           {
                                             bindings =
                                               (uu___145_10539.bindings);
                                             depth = (uu___145_10539.depth);
                                             tcenv = (uu___145_10539.tcenv);
                                             warn = (uu___145_10539.warn);
                                             cache = (uu___145_10539.cache);
                                             nolabels =
                                               (uu___145_10539.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10539.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10539.current_module_name)
                                           }  in
                                         let uu____10540 =
                                           let uu____10541 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____10541  in
                                         if uu____10540
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____10535 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10551::uu____10552 ->
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
                                                   let uu____10575 =
                                                     let uu____10581 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing
                                                        in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10581)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10575
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10595 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                              in
                                           let uu____10597 =
                                             match formals with
                                             | [] ->
                                                 let uu____10606 =
                                                   let uu____10607 =
                                                     let uu____10609 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10609
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____10607
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10606)
                                             | uu____10612 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____10617 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10617
                                                    in
                                                 let name_tok_corr =
                                                   let uu____10619 =
                                                     let uu____10623 =
                                                       let uu____10624 =
                                                         let uu____10630 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10630)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10624
                                                        in
                                                     (uu____10623,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10619
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____10597 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10514 with
                                      | (decls2,env2) ->
                                          let uu____10654 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____10659 =
                                              encode_term res_t1 env'  in
                                            match uu____10659 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10667 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____10667,
                                                  decls)
                                             in
                                          (match uu____10654 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10675 =
                                                   let uu____10679 =
                                                     let uu____10680 =
                                                       let uu____10686 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____10686)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10680
                                                      in
                                                   (uu____10679,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10675
                                                  in
                                               let freshness =
                                                 let uu____10695 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____10695
                                                 then
                                                   let uu____10698 =
                                                     let uu____10699 =
                                                       let uu____10705 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd)
                                                          in
                                                       let uu____10711 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____10705,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10711)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10699
                                                      in
                                                   let uu____10713 =
                                                     let uu____10715 =
                                                       pretype_axiom env2
                                                         vapp vars
                                                        in
                                                     [uu____10715]  in
                                                   uu____10698 :: uu____10713
                                                 else []  in
                                               let g =
                                                 let uu____10719 =
                                                   let uu____10721 =
                                                     let uu____10723 =
                                                       let uu____10725 =
                                                         let uu____10727 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____10727
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10725
                                                        in
                                                     FStar_List.append decls3
                                                       uu____10723
                                                      in
                                                   FStar_List.append decls2
                                                     uu____10721
                                                    in
                                                 FStar_List.append decls11
                                                   uu____10719
                                                  in
                                               (g, env2))))))))
  
let declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string * FStar_SMTEncoding_Term.term option) *
            FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10749 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____10749 with
          | None  ->
              let uu____10772 = encode_free_var env x t t_norm []  in
              (match uu____10772 with
               | (decls,env1) ->
                   let uu____10787 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____10787 with
                    | (n1,x',uu____10806) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10818) -> ((n1, x1), [], env)
  
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
          let uu____10851 = encode_free_var env lid t tt quals  in
          match uu____10851 with
          | (decls,env1) ->
              let uu____10862 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____10862
              then
                let uu____10866 =
                  let uu____10868 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____10868  in
                (uu____10866, env1)
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
             (fun uu____10896  ->
                fun lb  ->
                  match uu____10896 with
                  | (decls,env1) ->
                      let uu____10908 =
                        let uu____10912 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____10912
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____10908 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____10926 = FStar_Syntax_Util.head_and_args t  in
    match uu____10926 with
    | (hd1,args) ->
        let uu____10952 =
          let uu____10953 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10953.FStar_Syntax_Syntax.n  in
        (match uu____10952 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10957,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10970 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____10985  ->
      fun quals  ->
        match uu____10985 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____11034 = FStar_Util.first_N nbinders formals  in
              match uu____11034 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11074  ->
                         fun uu____11075  ->
                           match (uu____11074, uu____11075) with
                           | ((formal,uu____11085),(binder,uu____11087)) ->
                               let uu____11092 =
                                 let uu____11097 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____11097)  in
                               FStar_Syntax_Syntax.NT uu____11092) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____11102 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11116  ->
                              match uu____11116 with
                              | (x,i) ->
                                  let uu____11123 =
                                    let uu___146_11124 = x  in
                                    let uu____11125 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11124.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11124.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11125
                                    }  in
                                  (uu____11123, i)))
                       in
                    FStar_All.pipe_right uu____11102
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____11137 =
                      let uu____11139 =
                        let uu____11140 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____11140.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11139
                       in
                    let uu____11144 =
                      let uu____11145 = FStar_Syntax_Subst.compress body  in
                      let uu____11146 =
                        let uu____11147 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11147
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____11145
                        uu____11146
                       in
                    uu____11144 uu____11137 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11189 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____11189
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11190 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11190.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11190.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11190.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11190.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11190.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11190.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11190.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11190.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11190.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11190.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11190.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11190.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11190.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11190.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11190.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11190.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11190.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11190.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11190.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11190.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11190.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11190.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11190.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____11211 = FStar_Syntax_Util.abs_formals e  in
                match uu____11211 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11260::uu____11261 ->
                         let uu____11269 =
                           let uu____11270 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11270.FStar_Syntax_Syntax.n  in
                         (match uu____11269 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11297 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11297 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11323 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11323
                                   then
                                     let uu____11341 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11341 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11387  ->
                                                   fun uu____11388  ->
                                                     match (uu____11387,
                                                             uu____11388)
                                                     with
                                                     | ((x,uu____11398),
                                                        (b,uu____11400)) ->
                                                         let uu____11405 =
                                                           let uu____11410 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11410)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11405)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11412 =
                                            let uu____11423 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11423)
                                             in
                                          (uu____11412, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11458 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11458 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11510) ->
                              let uu____11515 =
                                let uu____11526 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                fst uu____11526  in
                              (uu____11515, true)
                          | uu____11559 when Prims.op_Negation norm1 ->
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
                          | uu____11561 ->
                              let uu____11562 =
                                let uu____11563 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____11564 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11563
                                  uu____11564
                                 in
                              failwith uu____11562)
                     | uu____11577 ->
                         let uu____11578 =
                           let uu____11579 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11579.FStar_Syntax_Syntax.n  in
                         (match uu____11578 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11606 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11606 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____11624 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____11624 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11672 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____11700 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____11700
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11707 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11748  ->
                            fun lb  ->
                              match uu____11748 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11799 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____11799
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____11802 =
                                      let uu____11810 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____11810
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____11802 with
                                    | (tok,decl,env2) ->
                                        let uu____11835 =
                                          let uu____11842 =
                                            let uu____11848 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____11848, tok)  in
                                          uu____11842 :: toks  in
                                        (uu____11835, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____11707 with
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
                        | uu____11950 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11955 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____11955 vars)
                            else
                              (let uu____11957 =
                                 let uu____11961 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____11961)  in
                               FStar_SMTEncoding_Util.mkApp uu____11957)
                         in
                      let uu____11966 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11968  ->
                                 match uu___116_11968 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11969 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11972 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11972)))
                         in
                      if uu____11966
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11992;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11994;
                                FStar_Syntax_Syntax.lbeff = uu____11995;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____12036 =
                                 let uu____12040 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm]
                                    in
                                 match uu____12040 with
                                 | (tcenv',uu____12051,e_t) ->
                                     let uu____12055 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12062 -> failwith "Impossible"
                                        in
                                     (match uu____12055 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12071 = env1  in
                                            {
                                              bindings =
                                                (uu___150_12071.bindings);
                                              depth = (uu___150_12071.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12071.warn);
                                              cache = (uu___150_12071.cache);
                                              nolabels =
                                                (uu___150_12071.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12071.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12071.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12071.current_module_name)
                                            }), e1, t_norm1))
                                  in
                               (match uu____12036 with
                                | (env',e1,t_norm1) ->
                                    let uu____12078 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____12078 with
                                     | ((binders,body,uu____12090,uu____12091),curry)
                                         ->
                                         ((let uu____12098 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____12098
                                           then
                                             let uu____12099 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____12100 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12099 uu____12100
                                           else ());
                                          (let uu____12102 =
                                             encode_binders None binders env'
                                              in
                                           match uu____12102 with
                                           | (vars,guards,env'1,binder_decls,uu____12118)
                                               ->
                                               let body1 =
                                                 let uu____12126 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____12126
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____12129 =
                                                 let uu____12134 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____12134
                                                 then
                                                   let uu____12140 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____12141 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____12140, uu____12141)
                                                 else
                                                   (let uu____12147 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____12147))
                                                  in
                                               (match uu____12129 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12161 =
                                                        let uu____12165 =
                                                          let uu____12166 =
                                                            let uu____12172 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____12172)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12166
                                                           in
                                                        let uu____12178 =
                                                          let uu____12180 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____12180
                                                           in
                                                        (uu____12165,
                                                          uu____12178,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12161
                                                       in
                                                    let uu____12182 =
                                                      let uu____12184 =
                                                        let uu____12186 =
                                                          let uu____12188 =
                                                            let uu____12190 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12190
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12188
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12186
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____12184
                                                       in
                                                    (uu____12182, env1))))))
                           | uu____12193 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12212 = varops.fresh "fuel"  in
                             (uu____12212, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____12215 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12254  ->
                                     fun uu____12255  ->
                                       match (uu____12254, uu____12255) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12337 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12337  in
                                           let gtok =
                                             let uu____12339 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12339  in
                                           let env3 =
                                             let uu____12341 =
                                               let uu____12343 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12343
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12341
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____12215 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12429
                                 t_norm uu____12431 =
                                 match (uu____12429, uu____12431) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12458;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12459;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12476 =
                                       let uu____12480 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm]
                                          in
                                       match uu____12480 with
                                       | (tcenv',uu____12495,e_t) ->
                                           let uu____12499 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12506 ->
                                                 failwith "Impossible"
                                              in
                                           (match uu____12499 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12515 = env2
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___151_12515.bindings);
                                                    depth =
                                                      (uu___151_12515.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12515.warn);
                                                    cache =
                                                      (uu___151_12515.cache);
                                                    nolabels =
                                                      (uu___151_12515.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12515.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12515.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12515.current_module_name)
                                                  }), e1, t_norm1))
                                        in
                                     (match uu____12476 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12525 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____12525
                                            then
                                              let uu____12526 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____12527 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____12528 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12526 uu____12527
                                                uu____12528
                                            else ());
                                           (let uu____12530 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____12530 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12552 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____12552
                                                  then
                                                    let uu____12553 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____12554 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____12555 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____12556 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12553 uu____12554
                                                      uu____12555 uu____12556
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12560 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____12560 with
                                                  | (vars,guards,env'1,binder_decls,uu____12578)
                                                      ->
                                                      let decl_g =
                                                        let uu____12586 =
                                                          let uu____12592 =
                                                            let uu____12594 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12594
                                                             in
                                                          (g, uu____12592,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12586
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
                                                        let uu____12609 =
                                                          let uu____12613 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____12613)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12609
                                                         in
                                                      let gsapp =
                                                        let uu____12619 =
                                                          let uu____12623 =
                                                            let uu____12625 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____12625 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12623)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12619
                                                         in
                                                      let gmax =
                                                        let uu____12629 =
                                                          let uu____12633 =
                                                            let uu____12635 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____12635 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____12633)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12629
                                                         in
                                                      let body1 =
                                                        let uu____12639 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____12639
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____12641 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____12641 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12652
                                                               =
                                                               let uu____12656
                                                                 =
                                                                 let uu____12657
                                                                   =
                                                                   let uu____12665
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
                                                                    uu____12665)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12657
                                                                  in
                                                               let uu____12676
                                                                 =
                                                                 let uu____12678
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____12678
                                                                  in
                                                               (uu____12656,
                                                                 uu____12676,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12652
                                                              in
                                                           let eqn_f =
                                                             let uu____12681
                                                               =
                                                               let uu____12685
                                                                 =
                                                                 let uu____12686
                                                                   =
                                                                   let uu____12692
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12692)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12686
                                                                  in
                                                               (uu____12685,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12681
                                                              in
                                                           let eqn_g' =
                                                             let uu____12700
                                                               =
                                                               let uu____12704
                                                                 =
                                                                 let uu____12705
                                                                   =
                                                                   let uu____12711
                                                                    =
                                                                    let uu____12712
                                                                    =
                                                                    let uu____12715
                                                                    =
                                                                    let uu____12716
                                                                    =
                                                                    let uu____12720
                                                                    =
                                                                    let uu____12722
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____12722
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____12720)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12716
                                                                     in
                                                                    (gsapp,
                                                                    uu____12715)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12712
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12711)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12705
                                                                  in
                                                               (uu____12704,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12700
                                                              in
                                                           let uu____12734 =
                                                             let uu____12739
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____12739
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12756)
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
                                                                    let uu____12771
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____12771
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____12774
                                                                    =
                                                                    let uu____12778
                                                                    =
                                                                    let uu____12779
                                                                    =
                                                                    let uu____12785
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12785)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12779
                                                                     in
                                                                    (uu____12778,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12774
                                                                    in
                                                                 let uu____12796
                                                                   =
                                                                   let uu____12800
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____12800
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12808
                                                                    =
                                                                    let uu____12810
                                                                    =
                                                                    let uu____12811
                                                                    =
                                                                    let uu____12815
                                                                    =
                                                                    let uu____12816
                                                                    =
                                                                    let uu____12822
                                                                    =
                                                                    let uu____12823
                                                                    =
                                                                    let uu____12826
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____12826,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12823
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12822)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12816
                                                                     in
                                                                    (uu____12815,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12811
                                                                     in
                                                                    [uu____12810]
                                                                     in
                                                                    (d3,
                                                                    uu____12808)
                                                                    in
                                                                 (match uu____12796
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
                                                           (match uu____12734
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
                               let uu____12861 =
                                 let uu____12868 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____12904  ->
                                      fun uu____12905  ->
                                        match (uu____12904, uu____12905) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12991 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____12991 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12868
                                  in
                               (match uu____12861 with
                                | (decls2,eqns,env01) ->
                                    let uu____13031 =
                                      let isDeclFun uu___117_13039 =
                                        match uu___117_13039 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13040 -> true
                                        | uu____13046 -> false  in
                                      let uu____13047 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____13047
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____13031 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13074 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____13074
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
      let nm =
        let uu____13107 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____13107 with | None  -> "" | Some l -> l.FStar_Ident.str
         in
      let uu____13110 = encode_sigelt' env se  in
      match uu____13110 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13120 =
                  let uu____13121 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____13121  in
                [uu____13120]
            | uu____13122 ->
                let uu____13123 =
                  let uu____13125 =
                    let uu____13126 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____13126  in
                  uu____13125 :: g  in
                let uu____13127 =
                  let uu____13129 =
                    let uu____13130 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____13130  in
                  [uu____13129]  in
                FStar_List.append uu____13123 uu____13127
             in
          (g1, env1)

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13138 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13141 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13143 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13145 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13153 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13156 =
            let uu____13157 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____13157 Prims.op_Negation  in
          if uu____13156
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13177 ->
                   let uu____13178 =
                     let uu____13181 =
                       let uu____13182 =
                         let uu____13197 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL]))
                            in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13197)
                          in
                       FStar_Syntax_Syntax.Tm_abs uu____13182  in
                     FStar_Syntax_Syntax.mk uu____13181  in
                   uu____13178 None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____13250 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____13250 with
               | (aname,atok,env2) ->
                   let uu____13260 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____13260 with
                    | (formals,uu____13270) ->
                        let uu____13277 =
                          let uu____13280 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____13280 env2  in
                        (match uu____13277 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13288 =
                                 let uu____13289 =
                                   let uu____13295 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13303  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13295,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____13289
                                  in
                               [uu____13288;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13310 =
                               let aux uu____13339 uu____13340 =
                                 match (uu____13339, uu____13340) with
                                 | ((bv,uu____13367),(env3,acc_sorts,acc)) ->
                                     let uu____13388 = gen_term_var env3 bv
                                        in
                                     (match uu____13388 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13310 with
                              | (uu____13426,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13440 =
                                      let uu____13444 =
                                        let uu____13445 =
                                          let uu____13451 =
                                            let uu____13452 =
                                              let uu____13455 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13455)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13452
                                             in
                                          ([[app]], xs_sorts, uu____13451)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13445
                                         in
                                      (uu____13444, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13440
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13467 =
                                      let uu____13471 =
                                        let uu____13472 =
                                          let uu____13478 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13478)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13472
                                         in
                                      (uu____13471,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13467
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13488 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13488 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13504,uu____13505)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13506 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13506 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13517,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____13522 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13524  ->
                      match uu___118_13524 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13525 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13528 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13529 -> false))
               in
            Prims.op_Negation uu____13522  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13535 = encode_top_level_val env fv t quals  in
             match uu____13535 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____13547 =
                   let uu____13549 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____13549  in
                 (uu____13547, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13554 = encode_formula f env  in
          (match uu____13554 with
           | (f1,decls) ->
               let g =
                 let uu____13563 =
                   let uu____13564 =
                     let uu____13568 =
                       let uu____13570 =
                         let uu____13571 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____13571  in
                       Some uu____13570  in
                     let uu____13572 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____13568, uu____13572)  in
                   FStar_SMTEncoding_Util.mkAssume uu____13564  in
                 [uu____13563]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13576,uu____13577) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13583 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13590 =
                       let uu____13595 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____13595.FStar_Syntax_Syntax.fv_name  in
                     uu____13590.FStar_Syntax_Syntax.v  in
                   let uu____13599 =
                     let uu____13600 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____13600  in
                   if uu____13599
                   then
                     let val_decl =
                       let uu___152_13615 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13615.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13615.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13615.FStar_Syntax_Syntax.sigmeta)
                       }  in
                     let uu____13619 = encode_sigelt' env1 val_decl  in
                     match uu____13619 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs)
             in
          (match uu____13583 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13636,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13638;
                          FStar_Syntax_Syntax.lbtyp = uu____13639;
                          FStar_Syntax_Syntax.lbeff = uu____13640;
                          FStar_Syntax_Syntax.lbdef = uu____13641;_}::[]),uu____13642,uu____13643)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13657 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____13657 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____13680 =
                   let uu____13682 =
                     let uu____13683 =
                       let uu____13687 =
                         let uu____13688 =
                           let uu____13694 =
                             let uu____13695 =
                               let uu____13698 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____13698)  in
                             FStar_SMTEncoding_Util.mkEq uu____13695  in
                           ([[b2t_x]], [xx], uu____13694)  in
                         FStar_SMTEncoding_Util.mkForall uu____13688  in
                       (uu____13687, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Util.mkAssume uu____13683  in
                   [uu____13682]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13680
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13715,uu____13716,uu____13717)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13723  ->
                  match uu___119_13723 with
                  | FStar_Syntax_Syntax.Discriminator uu____13724 -> true
                  | uu____13725 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13727,lids,uu____13729) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13736 =
                     let uu____13737 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____13737.FStar_Ident.idText  in
                   uu____13736 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13739  ->
                     match uu___120_13739 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13740 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13743,uu____13744)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13754  ->
                  match uu___121_13754 with
                  | FStar_Syntax_Syntax.Projector uu____13755 -> true
                  | uu____13758 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____13765 = try_lookup_free_var env l  in
          (match uu____13765 with
           | Some uu____13769 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13772 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13772.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13772.FStar_Syntax_Syntax.sigmeta)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13778,uu____13779) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13791) ->
          let uu____13796 = encode_sigelts env ses  in
          (match uu____13796 with
           | (g,env1) ->
               let uu____13806 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13816  ->
                         match uu___122_13816 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13817;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13818;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13819;_}
                             -> false
                         | uu____13821 -> true))
                  in
               (match uu____13806 with
                | (g',inversions) ->
                    let uu____13830 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13840  ->
                              match uu___123_13840 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13841 ->
                                  true
                              | uu____13847 -> false))
                       in
                    (match uu____13830 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13858,tps,k,uu____13861,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13871  ->
                    match uu___124_13871 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13872 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13879 = c  in
              match uu____13879 with
              | (name,args,uu____13883,uu____13884,uu____13885) ->
                  let uu____13888 =
                    let uu____13889 =
                      let uu____13895 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13902  ->
                                match uu____13902 with
                                | (uu____13906,sort,uu____13908) -> sort))
                         in
                      (name, uu____13895, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13889  in
                  [uu____13888]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____13926 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13929 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____13929 FStar_Option.isNone))
               in
            if uu____13926
            then []
            else
              (let uu____13946 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____13946 with
               | (xxsym,xx) ->
                   let uu____13952 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13963  ->
                             fun l  ->
                               match uu____13963 with
                               | (out,decls) ->
                                   let uu____13975 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____13975 with
                                    | (uu____13981,data_t) ->
                                        let uu____13983 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____13983 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14012 =
                                                 let uu____14013 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____14013.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____14012 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14021,indices) ->
                                                   indices
                                               | uu____14037 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14049  ->
                                                         match uu____14049
                                                         with
                                                         | (x,uu____14053) ->
                                                             let uu____14054
                                                               =
                                                               let uu____14055
                                                                 =
                                                                 let uu____14059
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____14059,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14055
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____14054)
                                                    env)
                                                in
                                             let uu____14061 =
                                               encode_args indices env1  in
                                             (match uu____14061 with
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
                                                      let uu____14081 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14089
                                                                 =
                                                                 let uu____14092
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____14092,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14089)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____14081
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____14094 =
                                                      let uu____14095 =
                                                        let uu____14098 =
                                                          let uu____14099 =
                                                            let uu____14102 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____14102,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14099
                                                           in
                                                        (out, uu____14098)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14095
                                                       in
                                                    (uu____14094,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____13952 with
                    | (data_ax,decls) ->
                        let uu____14110 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____14110 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14121 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14121 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____14124 =
                                 let uu____14128 =
                                   let uu____14129 =
                                     let uu____14135 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____14143 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____14135,
                                       uu____14143)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14129
                                    in
                                 let uu____14151 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____14128, (Some "inversion axiom"),
                                   uu____14151)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____14124
                                in
                             let pattern_guarded_inversion =
                               let uu____14155 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____14155
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____14163 =
                                   let uu____14164 =
                                     let uu____14168 =
                                       let uu____14169 =
                                         let uu____14175 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____14183 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14175, uu____14183)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14169
                                        in
                                     let uu____14191 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____14168, (Some "inversion axiom"),
                                       uu____14191)
                                      in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14164
                                    in
                                 [uu____14163]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____14194 =
            let uu____14202 =
              let uu____14203 = FStar_Syntax_Subst.compress k  in
              uu____14203.FStar_Syntax_Syntax.n  in
            match uu____14202 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14232 -> (tps, k)  in
          (match uu____14194 with
           | (formals,res) ->
               let uu____14247 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____14247 with
                | (formals1,res1) ->
                    let uu____14254 = encode_binders None formals1 env  in
                    (match uu____14254 with
                     | (vars,guards,env',binder_decls,uu____14269) ->
                         let uu____14276 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14276 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14289 =
                                  let uu____14293 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14293)  in
                                FStar_SMTEncoding_Util.mkApp uu____14289  in
                              let uu____14298 =
                                let tname_decl =
                                  let uu____14304 =
                                    let uu____14305 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14320  ->
                                              match uu____14320 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14328 = varops.next_id ()  in
                                    (tname, uu____14305,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14328, false)
                                     in
                                  constructor_or_logic_type_decl uu____14304
                                   in
                                let uu____14333 =
                                  match vars with
                                  | [] ->
                                      let uu____14340 =
                                        let uu____14341 =
                                          let uu____14343 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14343
                                           in
                                        push_free_var env1 t tname
                                          uu____14341
                                         in
                                      ([], uu____14340)
                                  | uu____14347 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14353 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14353
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14362 =
                                          let uu____14366 =
                                            let uu____14367 =
                                              let uu____14375 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14375)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14367
                                             in
                                          (uu____14366,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14362
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14333 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14298 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14398 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14398 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14412 =
                                               let uu____14413 =
                                                 let uu____14417 =
                                                   let uu____14418 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14418
                                                    in
                                                 (uu____14417,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14413
                                                in
                                             [uu____14412]
                                           else []  in
                                         let uu____14421 =
                                           let uu____14423 =
                                             let uu____14425 =
                                               let uu____14426 =
                                                 let uu____14430 =
                                                   let uu____14431 =
                                                     let uu____14437 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14437)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14431
                                                    in
                                                 (uu____14430, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14426
                                                in
                                             [uu____14425]  in
                                           FStar_List.append karr uu____14423
                                            in
                                         FStar_List.append decls1 uu____14421
                                      in
                                   let aux =
                                     let uu____14446 =
                                       let uu____14448 =
                                         inversion_axioms tapp vars  in
                                       let uu____14450 =
                                         let uu____14452 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____14452]  in
                                       FStar_List.append uu____14448
                                         uu____14450
                                        in
                                     FStar_List.append kindingAx uu____14446
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14457,uu____14458,uu____14459,uu____14460,uu____14461)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14466,t,uu____14468,n_tps,uu____14470) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____14475 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14475 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14486 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14486 with
                | (formals,t_res) ->
                    let uu____14508 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14508 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14517 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14517 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____14555 =
                                            mk_term_projector_name d x  in
                                          (uu____14555,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____14557 =
                                  let uu____14567 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14567, true)
                                   in
                                FStar_All.pipe_right uu____14557
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
                              let uu____14589 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____14589 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14597::uu____14598 ->
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
                                         let uu____14623 =
                                           let uu____14629 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14629)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14623
                                     | uu____14642 -> tok_typing  in
                                   let uu____14647 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____14647 with
                                    | (vars',guards',env'',decls_formals,uu____14662)
                                        ->
                                        let uu____14669 =
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
                                        (match uu____14669 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14688 ->
                                                   let uu____14692 =
                                                     let uu____14693 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14693
                                                      in
                                                   [uu____14692]
                                                in
                                             let encode_elim uu____14700 =
                                               let uu____14701 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____14701 with
                                               | (head1,args) ->
                                                   let uu____14730 =
                                                     let uu____14731 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____14731.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____14730 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14738;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14739;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14740;_},uu____14741)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____14751 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____14751
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
                                                                 | uu____14777
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
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14786
                                                                     in
                                                                    if
                                                                    uu____14785
                                                                    then
                                                                    let uu____14793
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____14793]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____14795
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14808
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14808
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14830
                                                                    =
                                                                    let uu____14834
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14834
                                                                     in
                                                                    (match uu____14830
                                                                    with
                                                                    | 
                                                                    (uu____14841,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14847
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____14847
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14849
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____14849
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
                                                             (match uu____14795
                                                              with
                                                              | (uu____14857,arg_vars,elim_eqns_or_guards,uu____14860)
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
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14883
                                                                    =
                                                                    let uu____14884
                                                                    =
                                                                    let uu____14890
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14896
                                                                    =
                                                                    let uu____14897
                                                                    =
                                                                    let uu____14900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____14900)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14897
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14890,
                                                                    uu____14896)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14884
                                                                     in
                                                                    (uu____14883,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14879
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14913
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____14913,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____14915
                                                                    =
                                                                    let uu____14919
                                                                    =
                                                                    let uu____14920
                                                                    =
                                                                    let uu____14926
                                                                    =
                                                                    let uu____14929
                                                                    =
                                                                    let uu____14931
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____14931]
                                                                     in
                                                                    [uu____14929]
                                                                     in
                                                                    let uu____14934
                                                                    =
                                                                    let uu____14935
                                                                    =
                                                                    let uu____14938
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____14939
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____14938,
                                                                    uu____14939)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14935
                                                                     in
                                                                    (uu____14926,
                                                                    [x],
                                                                    uu____14934)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14920
                                                                     in
                                                                    let uu____14949
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____14919,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14949)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14915
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14954
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
                                                                    (let uu____14969
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14970
                                                                    dapp1  in
                                                                    [uu____14969])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____14954
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____14974
                                                                    =
                                                                    let uu____14978
                                                                    =
                                                                    let uu____14979
                                                                    =
                                                                    let uu____14985
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____14991
                                                                    =
                                                                    let uu____14992
                                                                    =
                                                                    let uu____14995
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____14995)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14992
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14985,
                                                                    uu____14991)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14979
                                                                     in
                                                                    (uu____14978,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14974)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____15011 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____15011
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
                                                                 | uu____15037
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
                                                                    let uu____15045
                                                                    =
                                                                    let uu____15046
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15046
                                                                     in
                                                                    if
                                                                    uu____15045
                                                                    then
                                                                    let uu____15053
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15053]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____15055
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15068
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15068
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15090
                                                                    =
                                                                    let uu____15094
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15094
                                                                     in
                                                                    (match uu____15090
                                                                    with
                                                                    | 
                                                                    (uu____15101,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15107
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____15107
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15109
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15109
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
                                                             (match uu____15055
                                                              with
                                                              | (uu____15117,arg_vars,elim_eqns_or_guards,uu____15120)
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
                                                                    let uu____15139
                                                                    =
                                                                    let uu____15143
                                                                    =
                                                                    let uu____15144
                                                                    =
                                                                    let uu____15150
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15156
                                                                    =
                                                                    let uu____15157
                                                                    =
                                                                    let uu____15160
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15160)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15157
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15150,
                                                                    uu____15156)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15144
                                                                     in
                                                                    (uu____15143,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15139
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15173
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____15173,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15175
                                                                    =
                                                                    let uu____15179
                                                                    =
                                                                    let uu____15180
                                                                    =
                                                                    let uu____15186
                                                                    =
                                                                    let uu____15189
                                                                    =
                                                                    let uu____15191
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15191]
                                                                     in
                                                                    [uu____15189]
                                                                     in
                                                                    let uu____15194
                                                                    =
                                                                    let uu____15195
                                                                    =
                                                                    let uu____15198
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15199
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15198,
                                                                    uu____15199)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15195
                                                                     in
                                                                    (uu____15186,
                                                                    [x],
                                                                    uu____15194)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15180
                                                                     in
                                                                    let uu____15209
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15179,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15209)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15175
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15214
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
                                                                    (let uu____15229
                                                                    =
                                                                    let uu____15230
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15230
                                                                    dapp1  in
                                                                    [uu____15229])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15214
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15234
                                                                    =
                                                                    let uu____15238
                                                                    =
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15245
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15251
                                                                    =
                                                                    let uu____15252
                                                                    =
                                                                    let uu____15255
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15255)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15252
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15245,
                                                                    uu____15251)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15239
                                                                     in
                                                                    (uu____15238,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15234)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15265 ->
                                                        ((let uu____15267 =
                                                            let uu____15268 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____15269 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15268
                                                              uu____15269
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15267);
                                                         ([], [])))
                                                in
                                             let uu____15272 = encode_elim ()
                                                in
                                             (match uu____15272 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15284 =
                                                      let uu____15286 =
                                                        let uu____15288 =
                                                          let uu____15290 =
                                                            let uu____15292 =
                                                              let uu____15293
                                                                =
                                                                let uu____15299
                                                                  =
                                                                  let uu____15301
                                                                    =
                                                                    let uu____15302
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15302
                                                                     in
                                                                  Some
                                                                    uu____15301
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15299)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15293
                                                               in
                                                            [uu____15292]  in
                                                          let uu____15305 =
                                                            let uu____15307 =
                                                              let uu____15309
                                                                =
                                                                let uu____15311
                                                                  =
                                                                  let uu____15313
                                                                    =
                                                                    let uu____15315
                                                                    =
                                                                    let uu____15317
                                                                    =
                                                                    let uu____15318
                                                                    =
                                                                    let uu____15322
                                                                    =
                                                                    let uu____15323
                                                                    =
                                                                    let uu____15329
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15329)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15323
                                                                     in
                                                                    (uu____15322,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15318
                                                                     in
                                                                    let uu____15336
                                                                    =
                                                                    let uu____15338
                                                                    =
                                                                    let uu____15339
                                                                    =
                                                                    let uu____15343
                                                                    =
                                                                    let uu____15344
                                                                    =
                                                                    let uu____15350
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____15356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15350,
                                                                    uu____15356)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15344
                                                                     in
                                                                    (uu____15343,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15339
                                                                     in
                                                                    [uu____15338]
                                                                     in
                                                                    uu____15317
                                                                    ::
                                                                    uu____15336
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15315
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15313
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15311
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15309
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15307
                                                             in
                                                          FStar_List.append
                                                            uu____15290
                                                            uu____15305
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15288
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15286
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15284
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15377  ->
              fun se  ->
                match uu____15377 with
                | (g,env1) ->
                    let uu____15389 = encode_sigelt env1 se  in
                    (match uu____15389 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15425 =
        match uu____15425 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15443 ->
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
                 ((let uu____15448 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15448
                   then
                     let uu____15449 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15450 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15451 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15449 uu____15450 uu____15451
                   else ());
                  (let uu____15453 = encode_term t1 env1  in
                   match uu____15453 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15463 =
                         let uu____15467 =
                           let uu____15468 =
                             let uu____15469 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15469
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15468  in
                         new_term_constant_from_string env1 x uu____15467  in
                       (match uu____15463 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____15480 = FStar_Options.log_queries ()
                                 in
                              if uu____15480
                              then
                                let uu____15482 =
                                  let uu____15483 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15484 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15485 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15483 uu____15484 uu____15485
                                   in
                                Some uu____15482
                              else None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15496,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____15505 = encode_free_var env1 fv t t_norm []  in
                 (match uu____15505 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15518,se,uu____15520) ->
                 let uu____15523 = encode_sigelt env1 se  in
                 (match uu____15523 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15533,se) ->
                 let uu____15537 = encode_sigelt env1 se  in
                 (match uu____15537 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____15547 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____15547 with | (uu____15559,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15604  ->
            match uu____15604 with
            | (l,uu____15611,uu____15612) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15633  ->
            match uu____15633 with
            | (l,uu____15641,uu____15642) ->
                let uu____15647 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l)
                   in
                let uu____15648 =
                  let uu____15650 =
                    let uu____15651 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____15651  in
                  [uu____15650]  in
                uu____15647 :: uu____15648))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15662 =
      let uu____15664 =
        let uu____15665 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____15667 =
          let uu____15668 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____15668 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15665;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15667
        }  in
      [uu____15664]  in
    FStar_ST.write last_env uu____15662
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15678 = FStar_ST.read last_env  in
      match uu____15678 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15684 ->
          let uu___154_15686 = e  in
          let uu____15687 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___154_15686.bindings);
            depth = (uu___154_15686.depth);
            tcenv;
            warn = (uu___154_15686.warn);
            cache = (uu___154_15686.cache);
            nolabels = (uu___154_15686.nolabels);
            use_zfuel_name = (uu___154_15686.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15686.encode_non_total_function_typ);
            current_module_name = uu____15687
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____15691 = FStar_ST.read last_env  in
    match uu____15691 with
    | [] -> failwith "Empty env stack"
    | uu____15696::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____15704  ->
    let uu____15705 = FStar_ST.read last_env  in
    match uu____15705 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___155_15716 = hd1  in
          {
            bindings = (uu___155_15716.bindings);
            depth = (uu___155_15716.depth);
            tcenv = (uu___155_15716.tcenv);
            warn = (uu___155_15716.warn);
            cache = refs;
            nolabels = (uu___155_15716.nolabels);
            use_zfuel_name = (uu___155_15716.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15716.encode_non_total_function_typ);
            current_module_name = (uu___155_15716.current_module_name)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____15722  ->
    let uu____15723 = FStar_ST.read last_env  in
    match uu____15723 with
    | [] -> failwith "Popping an empty stack"
    | uu____15728::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____15736  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____15739  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____15742  ->
    let uu____15743 = FStar_ST.read last_env  in
    match uu____15743 with
    | hd1::uu____15749::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15755 -> failwith "Impossible"
  
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
  
let open_fact_db_tags : env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> [] 
let place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____15804::uu____15805,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15809 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15809.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15809.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15809.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15810 -> d
  
let fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15821 =
        let uu____15823 =
          let uu____15824 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____15824  in
        let uu____15825 = open_fact_db_tags env  in uu____15823 ::
          uu____15825
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15821
  
let encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____15840 = encode_sigelt env se  in
      match uu____15840 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15865 = FStar_Options.log_queries ()  in
        if uu____15865
        then
          let uu____15867 =
            let uu____15868 =
              let uu____15869 =
                let uu____15870 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____15870 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____15869  in
            FStar_SMTEncoding_Term.Caption uu____15868  in
          uu____15867 :: decls
        else decls  in
      let env =
        let uu____15877 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____15877 tcenv  in
      let uu____15878 = encode_top_level_facts env se  in
      match uu____15878 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15887 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____15887))
  
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
      (let uu____15898 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____15898
       then
         let uu____15899 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15899
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15920  ->
                 fun se  ->
                   match uu____15920 with
                   | (g,env2) ->
                       let uu____15932 = encode_top_level_facts env2 se  in
                       (match uu____15932 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____15945 =
         encode_signature
           (let uu___157_15949 = env  in
            {
              bindings = (uu___157_15949.bindings);
              depth = (uu___157_15949.depth);
              tcenv = (uu___157_15949.tcenv);
              warn = false;
              cache = (uu___157_15949.cache);
              nolabels = (uu___157_15949.nolabels);
              use_zfuel_name = (uu___157_15949.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15949.encode_non_total_function_typ);
              current_module_name = (uu___157_15949.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____15945 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15961 = FStar_Options.log_queries ()  in
             if uu____15961
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___158_15966 = env1  in
               {
                 bindings = (uu___158_15966.bindings);
                 depth = (uu___158_15966.depth);
                 tcenv = (uu___158_15966.tcenv);
                 warn = true;
                 cache = (uu___158_15966.cache);
                 nolabels = (uu___158_15966.nolabels);
                 use_zfuel_name = (uu___158_15966.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15966.encode_non_total_function_typ);
                 current_module_name = (uu___158_15966.current_module_name)
               });
            (let uu____15968 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____15968
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let encode_query :
  (Prims.unit -> Prims.string) option ->
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
        (let uu____16003 =
           let uu____16004 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16004.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16003);
        (let env =
           let uu____16006 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16006 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____16013 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16034 = aux rest  in
                 (match uu____16034 with
                  | (out,rest1) ->
                      let t =
                        let uu____16052 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16052 with
                        | Some uu____16056 ->
                            let uu____16057 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16057
                              x.FStar_Syntax_Syntax.sort
                        | uu____16058 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____16061 =
                        let uu____16063 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16064 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16064.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16064.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16063 :: out  in
                      (uu____16061, rest1))
             | uu____16067 -> ([], bindings1)  in
           let uu____16071 = aux bindings  in
           match uu____16071 with
           | (closing,bindings1) ->
               let uu____16085 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16085, bindings1)
            in
         match uu____16013 with
         | (q1,bindings1) ->
             let uu____16098 =
               let uu____16101 =
                 FStar_List.filter
                   (fun uu___125_16103  ->
                      match uu___125_16103 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16104 ->
                          false
                      | uu____16108 -> true) bindings1
                  in
               encode_env_bindings env uu____16101  in
             (match uu____16098 with
              | (env_decls,env1) ->
                  ((let uu____16119 =
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
                    if uu____16119
                    then
                      let uu____16120 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16120
                    else ());
                   (let uu____16122 = encode_formula q1 env1  in
                    match uu____16122 with
                    | (phi,qdecls) ->
                        let uu____16134 =
                          let uu____16137 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16137 phi
                           in
                        (match uu____16134 with
                         | (labels,phi1) ->
                             let uu____16147 = encode_labels labels  in
                             (match uu____16147 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____16168 =
                                      let uu____16172 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16173 =
                                        varops.mk_unique "@query"  in
                                      (uu____16172, (Some "query"),
                                        uu____16173)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16168
                                     in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"]
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16186 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____16186 tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16188 = encode_formula q env  in
       match uu____16188 with
       | (f,uu____16192) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16194) -> true
             | uu____16197 -> false)))
  