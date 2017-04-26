open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme)
  | Binding_sig of (FStar_Ident.lident Prims.list*
  FStar_Syntax_Syntax.sigelt)
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of (FStar_Ident.lident Prims.list*
  FStar_Syntax_Syntax.sigelt* FStar_Syntax_Syntax.universes)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____29 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____43 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____64 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____85 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____101 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt*
      FStar_Syntax_Syntax.universes)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____127 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____131 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____135 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____140 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      Prims.option;}
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident* FStar_Ident.lident* FStar_Ident.lident* mlift*
      mlift) Prims.list;}
type cached_elt =
  (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                               FStar_Syntax_Syntax.universes
                                                               Prims.option))
    FStar_Util.either* FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ Prims.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs: (FStar_Syntax_Syntax.lbname* FStar_Syntax_Syntax.typ) Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ* guard_t);
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index: (FStar_Ident.lident* Prims.int) Prims.option;}
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  mark: Prims.string -> Prims.unit;
  reset_mark: Prims.string -> Prims.unit;
  commit_mark: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess: env -> goal -> (env* goal) Prims.list;
  solve:
    (Prims.unit -> Prims.string) Prims.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list*
      FStar_TypeChecker_Common.univ_ineq Prims.list);
  implicits:
    (Prims.string* env* FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.term*
      FStar_Syntax_Syntax.typ* FStar_Range.range) Prims.list;}
type implicits =
  (Prims.string* env* FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.term*
    FStar_Syntax_Syntax.typ* FStar_Range.range) Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,_)
        |(Eager_unfolding_only
          ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
         |(Unfold _,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          |(Unfold _,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____848 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____858 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____866 =
  FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.typ* guard_t))
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____905 = new_gamma_cache () in
          let uu____907 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____905;
            modules = [];
            expected_typ = None;
            sigtab = uu____907;
            is_pattern = false;
            instantiate_imp = true;
            effects = { decls = []; order = []; joins = [] };
            generalize = true;
            letrecs = [];
            top_level = false;
            check_uvars = false;
            use_eq = false;
            is_iface = false;
            admit = false;
            lax = false;
            lax_universes = false;
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = None
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____950  ->
    let uu____951 = FStar_ST.read query_indices in
    match uu____951 with
    | [] -> failwith "Empty query indices!"
    | uu____965 ->
        let uu____970 =
          let uu____975 =
            let uu____979 = FStar_ST.read query_indices in
            FStar_List.hd uu____979 in
          let uu____993 = FStar_ST.read query_indices in uu____975 ::
            uu____993 in
        FStar_ST.write query_indices uu____970
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1015  ->
    let uu____1016 = FStar_ST.read query_indices in
    match uu____1016 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1052  ->
    match uu____1052 with
    | (l,n1) ->
        let uu____1057 = FStar_ST.read query_indices in
        (match uu____1057 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1091 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1101  ->
    let uu____1102 = FStar_ST.read query_indices in FStar_List.hd uu____1102
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1118  ->
    let uu____1119 = FStar_ST.read query_indices in
    match uu____1119 with
    | hd1::uu____1131::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1158 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1172 =
       let uu____1174 = FStar_ST.read stack in env :: uu____1174 in
     FStar_ST.write stack uu____1172);
    (let uu___113_1182 = env in
     let uu____1183 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1185 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___113_1182.solver);
       range = (uu___113_1182.range);
       curmodule = (uu___113_1182.curmodule);
       gamma = (uu___113_1182.gamma);
       gamma_cache = uu____1183;
       modules = (uu___113_1182.modules);
       expected_typ = (uu___113_1182.expected_typ);
       sigtab = uu____1185;
       is_pattern = (uu___113_1182.is_pattern);
       instantiate_imp = (uu___113_1182.instantiate_imp);
       effects = (uu___113_1182.effects);
       generalize = (uu___113_1182.generalize);
       letrecs = (uu___113_1182.letrecs);
       top_level = (uu___113_1182.top_level);
       check_uvars = (uu___113_1182.check_uvars);
       use_eq = (uu___113_1182.use_eq);
       is_iface = (uu___113_1182.is_iface);
       admit = (uu___113_1182.admit);
       lax = (uu___113_1182.lax);
       lax_universes = (uu___113_1182.lax_universes);
       type_of = (uu___113_1182.type_of);
       universe_of = (uu___113_1182.universe_of);
       use_bv_sorts = (uu___113_1182.use_bv_sorts);
       qname_and_index = (uu___113_1182.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1189  ->
    let uu____1190 = FStar_ST.read stack in
    match uu____1190 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1202 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let mark: env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
let commit_mark: env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____1234 = pop_stack () in ());
    env
let reset_mark: env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | None  -> env
    | Some (l,n1) ->
        let uu____1253 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1265  ->
                  match uu____1265 with
                  | (m,uu____1269) -> FStar_Ident.lid_equals l m)) in
        (match uu____1253 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1274 = env in
               {
                 solver = (uu___114_1274.solver);
                 range = (uu___114_1274.range);
                 curmodule = (uu___114_1274.curmodule);
                 gamma = (uu___114_1274.gamma);
                 gamma_cache = (uu___114_1274.gamma_cache);
                 modules = (uu___114_1274.modules);
                 expected_typ = (uu___114_1274.expected_typ);
                 sigtab = (uu___114_1274.sigtab);
                 is_pattern = (uu___114_1274.is_pattern);
                 instantiate_imp = (uu___114_1274.instantiate_imp);
                 effects = (uu___114_1274.effects);
                 generalize = (uu___114_1274.generalize);
                 letrecs = (uu___114_1274.letrecs);
                 top_level = (uu___114_1274.top_level);
                 check_uvars = (uu___114_1274.check_uvars);
                 use_eq = (uu___114_1274.use_eq);
                 is_iface = (uu___114_1274.is_iface);
                 admit = (uu___114_1274.admit);
                 lax = (uu___114_1274.lax);
                 lax_universes = (uu___114_1274.lax_universes);
                 type_of = (uu___114_1274.type_of);
                 universe_of = (uu___114_1274.universe_of);
                 use_bv_sorts = (uu___114_1274.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1277,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___115_1283 = env in
               {
                 solver = (uu___115_1283.solver);
                 range = (uu___115_1283.range);
                 curmodule = (uu___115_1283.curmodule);
                 gamma = (uu___115_1283.gamma);
                 gamma_cache = (uu___115_1283.gamma_cache);
                 modules = (uu___115_1283.modules);
                 expected_typ = (uu___115_1283.expected_typ);
                 sigtab = (uu___115_1283.sigtab);
                 is_pattern = (uu___115_1283.is_pattern);
                 instantiate_imp = (uu___115_1283.instantiate_imp);
                 effects = (uu___115_1283.effects);
                 generalize = (uu___115_1283.generalize);
                 letrecs = (uu___115_1283.letrecs);
                 top_level = (uu___115_1283.top_level);
                 check_uvars = (uu___115_1283.check_uvars);
                 use_eq = (uu___115_1283.use_eq);
                 is_iface = (uu___115_1283.is_iface);
                 admit = (uu___115_1283.admit);
                 lax = (uu___115_1283.lax);
                 lax_universes = (uu___115_1283.lax_universes);
                 type_of = (uu___115_1283.type_of);
                 universe_of = (uu___115_1283.universe_of);
                 use_bv_sorts = (uu___115_1283.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___116_1299 = e in
         {
           solver = (uu___116_1299.solver);
           range = r;
           curmodule = (uu___116_1299.curmodule);
           gamma = (uu___116_1299.gamma);
           gamma_cache = (uu___116_1299.gamma_cache);
           modules = (uu___116_1299.modules);
           expected_typ = (uu___116_1299.expected_typ);
           sigtab = (uu___116_1299.sigtab);
           is_pattern = (uu___116_1299.is_pattern);
           instantiate_imp = (uu___116_1299.instantiate_imp);
           effects = (uu___116_1299.effects);
           generalize = (uu___116_1299.generalize);
           letrecs = (uu___116_1299.letrecs);
           top_level = (uu___116_1299.top_level);
           check_uvars = (uu___116_1299.check_uvars);
           use_eq = (uu___116_1299.use_eq);
           is_iface = (uu___116_1299.is_iface);
           admit = (uu___116_1299.admit);
           lax = (uu___116_1299.lax);
           lax_universes = (uu___116_1299.lax_universes);
           type_of = (uu___116_1299.type_of);
           universe_of = (uu___116_1299.universe_of);
           use_bv_sorts = (uu___116_1299.use_bv_sorts);
           qname_and_index = (uu___116_1299.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___117_1316 = env in
      {
        solver = (uu___117_1316.solver);
        range = (uu___117_1316.range);
        curmodule = lid;
        gamma = (uu___117_1316.gamma);
        gamma_cache = (uu___117_1316.gamma_cache);
        modules = (uu___117_1316.modules);
        expected_typ = (uu___117_1316.expected_typ);
        sigtab = (uu___117_1316.sigtab);
        is_pattern = (uu___117_1316.is_pattern);
        instantiate_imp = (uu___117_1316.instantiate_imp);
        effects = (uu___117_1316.effects);
        generalize = (uu___117_1316.generalize);
        letrecs = (uu___117_1316.letrecs);
        top_level = (uu___117_1316.top_level);
        check_uvars = (uu___117_1316.check_uvars);
        use_eq = (uu___117_1316.use_eq);
        is_iface = (uu___117_1316.is_iface);
        admit = (uu___117_1316.admit);
        lax = (uu___117_1316.lax);
        lax_universes = (uu___117_1316.lax_universes);
        type_of = (uu___117_1316.type_of);
        universe_of = (uu___117_1316.universe_of);
        use_bv_sorts = (uu___117_1316.use_bv_sorts);
        qname_and_index = (uu___117_1316.qname_and_index)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt Prims.option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1338 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1338
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1341  ->
    let uu____1342 = FStar_Unionfind.fresh None in
    FStar_Syntax_Syntax.U_unif uu____1342
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1365) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1381 = FStar_Syntax_Subst.subst vs t in (us, uu____1381)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___101_1386  ->
    match uu___101_1386 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1400  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1410 = inst_tscheme t in
      match uu____1410 with
      | (us,t1) ->
          let uu____1417 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1417)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1429  ->
          match uu____1429 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1443 =
                         let uu____1444 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1447 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1450 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1451 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1444 uu____1447 uu____1450 uu____1451 in
                       failwith uu____1443)
                    else ();
                    (let uu____1453 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     Prims.snd uu____1453))
               | uu____1457 ->
                   let uu____1458 =
                     let uu____1459 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1459 in
                   failwith uu____1458)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1463 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1467 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1471 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____1497) -> Maybe
             | (uu____1501,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1513 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                                   FStar_Syntax_Syntax.universes
                                                                   Prims.option))
        FStar_Util.either* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t in
      let found =
        if cur_mod <> No
        then
          let uu____1573 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1573 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___102_1594  ->
                   match uu___102_1594 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1617 =
                           let uu____1627 =
                             let uu____1635 = inst_tscheme t in
                             FStar_Util.Inl uu____1635 in
                           (uu____1627, (FStar_Ident.range_of_lid l)) in
                         Some uu____1617
                       else None
                   | Binding_sig
                       (uu____1669,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1671);
                                     FStar_Syntax_Syntax.sigrng = uu____1672;
                                     FStar_Syntax_Syntax.sigqual = uu____1673;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1682 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1682
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1709 ->
                             Some t
                         | uu____1713 -> cache t in
                       let uu____1714 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1714 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1754 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1754 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1798 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1840 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1840
         then
           let uu____1851 = find_in_sigtab env lid in
           match uu____1851 with
           | Some se ->
               Some
                 ((FStar_Util.Inr (se, None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | None  -> None
         else None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1917) ->
          add_sigelts env ses
      | uu____1922 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____1931 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___103_1949  ->
           match uu___103_1949 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____1962 -> None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
        FStar_Range.range) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1983,lb::[]),uu____1985,uu____1986) ->
          let uu____1995 =
            let uu____2000 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2006 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2000, uu____2006) in
          Some uu____1995
      | FStar_Syntax_Syntax.Sig_let ((uu____2013,lbs),uu____2015,uu____2016)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2036 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2043 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2043
                   then
                     let uu____2049 =
                       let uu____2054 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2060 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2054, uu____2060) in
                     Some uu____2049
                   else None)
      | uu____2072 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) Prims.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2091 =
          let uu____2096 =
            let uu____2099 =
              let uu____2100 =
                let uu____2103 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2103 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2100) in
            inst_tscheme uu____2099 in
          (uu____2096, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2091
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2117,uu____2118) ->
        let uu____2121 =
          let uu____2126 =
            let uu____2129 =
              let uu____2130 =
                let uu____2133 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2133 in
              (us, uu____2130) in
            inst_tscheme uu____2129 in
          (uu____2126, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2121
    | uu____2144 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2179 =
        match uu____2179 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2229,uvs,t,uu____2232,uu____2233,uu____2234);
                    FStar_Syntax_Syntax.sigrng = uu____2235;
                    FStar_Syntax_Syntax.sigqual = uu____2236;_},None
                  )
                 ->
                 let uu____2246 =
                   let uu____2251 = inst_tscheme (uvs, t) in
                   (uu____2251, rng) in
                 Some uu____2246
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2263;
                    FStar_Syntax_Syntax.sigqual = qs;_},None
                  )
                 ->
                 let uu____2272 =
                   let uu____2273 = in_cur_mod env l in uu____2273 = Yes in
                 if uu____2272
                 then
                   let uu____2279 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2279
                    then
                      let uu____2286 =
                        let uu____2291 = inst_tscheme (uvs, t) in
                        (uu____2291, rng) in
                      Some uu____2286
                    else None)
                 else
                   (let uu____2306 =
                      let uu____2311 = inst_tscheme (uvs, t) in
                      (uu____2311, rng) in
                    Some uu____2306)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2324,uu____2325);
                    FStar_Syntax_Syntax.sigrng = uu____2326;
                    FStar_Syntax_Syntax.sigqual = uu____2327;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2346 =
                        let uu____2351 = inst_tscheme (uvs, k) in
                        (uu____2351, rng) in
                      Some uu____2346
                  | uu____2360 ->
                      let uu____2361 =
                        let uu____2366 =
                          let uu____2369 =
                            let uu____2370 =
                              let uu____2373 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2373 in
                            (uvs, uu____2370) in
                          inst_tscheme uu____2369 in
                        (uu____2366, rng) in
                      Some uu____2361)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2388,uu____2389);
                    FStar_Syntax_Syntax.sigrng = uu____2390;
                    FStar_Syntax_Syntax.sigqual = uu____2391;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2411 =
                        let uu____2416 = inst_tscheme_with (uvs, k) us in
                        (uu____2416, rng) in
                      Some uu____2411
                  | uu____2425 ->
                      let uu____2426 =
                        let uu____2431 =
                          let uu____2434 =
                            let uu____2435 =
                              let uu____2438 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2438 in
                            (uvs, uu____2435) in
                          inst_tscheme_with uu____2434 us in
                        (uu____2431, rng) in
                      Some uu____2426)
             | FStar_Util.Inr se ->
                 let uu____2458 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2469;
                        FStar_Syntax_Syntax.sigrng = uu____2470;
                        FStar_Syntax_Syntax.sigqual = uu____2471;_},None
                      ) -> lookup_type_of_let (Prims.fst se) lid
                   | uu____2480 -> effect_signature (Prims.fst se) in
                 FStar_All.pipe_right uu____2458
                   (FStar_Util.map_option
                      (fun uu____2503  ->
                         match uu____2503 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2520 =
        let uu____2526 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2526 mapper in
      match uu____2520 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___118_2578 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___118_2578.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___118_2578.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___118_2578.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2599 = lookup_qname env l in
      match uu____2599 with | None  -> false | Some uu____2619 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2647 = try_lookup_bv env bv in
      match uu____2647 with
      | None  ->
          let uu____2655 =
            let uu____2656 =
              let uu____2659 = variable_not_found bv in (uu____2659, bvr) in
            FStar_Errors.Error uu____2656 in
          Prims.raise uu____2655
      | Some (t,r) ->
          let uu____2666 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2667 = FStar_Range.set_use_range r bvr in
          (uu____2666, uu____2667)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2679 = try_lookup_lid_aux env l in
      match uu____2679 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2721 =
            let uu____2726 =
              let uu____2729 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2729) in
            (uu____2726, r1) in
          Some uu____2721
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2746 = try_lookup_lid env l in
      match uu____2746 with
      | None  ->
          let uu____2760 =
            let uu____2761 =
              let uu____2764 = name_not_found l in
              (uu____2764, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2761 in
          Prims.raise uu____2760
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___104_2785  ->
              match uu___104_2785 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2787 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2798 = lookup_qname env lid in
      match uu____2798 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2813,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2816;
              FStar_Syntax_Syntax.sigqual = q;_},None
            ),uu____2818)
          ->
          let uu____2842 =
            let uu____2848 =
              let uu____2851 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2851) in
            (uu____2848, q) in
          Some uu____2842
      | uu____2860 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2882 = lookup_qname env lid in
      match uu____2882 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2895,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2898;
              FStar_Syntax_Syntax.sigqual = uu____2899;_},None
            ),uu____2900)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2924 ->
          let uu____2935 =
            let uu____2936 =
              let uu____2939 = name_not_found lid in
              (uu____2939, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____2936 in
          Prims.raise uu____2935
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2950 = lookup_qname env lid in
      match uu____2950 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____2963,uvs,t,uu____2966,uu____2967,uu____2968);
              FStar_Syntax_Syntax.sigrng = uu____2969;
              FStar_Syntax_Syntax.sigqual = uu____2970;_},None
            ),uu____2971)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2997 ->
          let uu____3008 =
            let uu____3009 =
              let uu____3012 = name_not_found lid in
              (uu____3012, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3009 in
          Prims.raise uu____3008
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3024 = lookup_qname env lid in
      match uu____3024 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3038,uu____3039,uu____3040,uu____3041,uu____3042,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3044;
              FStar_Syntax_Syntax.sigqual = uu____3045;_},uu____3046),uu____3047)
          -> (true, dcs)
      | uu____3077 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3095 = lookup_qname env lid in
      match uu____3095 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3106,uu____3107,uu____3108,l,uu____3110,uu____3111);
              FStar_Syntax_Syntax.sigrng = uu____3112;
              FStar_Syntax_Syntax.sigqual = uu____3113;_},uu____3114),uu____3115)
          -> l
      | uu____3142 ->
          let uu____3153 =
            let uu____3154 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3154 in
          failwith uu____3153
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
          Prims.option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____3178 = lookup_qname env lid in
        match uu____3178 with
        | Some (FStar_Util.Inr (se,None ),uu____3193) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3219,lbs),uu____3221,uu____3222) when
                 visible se.FStar_Syntax_Syntax.sigqual ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3237 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3237
                      then
                        let uu____3242 =
                          let uu____3246 =
                            let uu____3247 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3247 in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3246) in
                        Some uu____3242
                      else None)
             | uu____3256 -> None)
        | uu____3259 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3280 = lookup_qname env ftv in
      match uu____3280 with
      | Some (FStar_Util.Inr (se,None ),uu____3293) ->
          let uu____3316 = effect_signature se in
          (match uu____3316 with
           | None  -> None
           | Some ((uu____3327,t),r) ->
               let uu____3336 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3336)
      | uu____3337 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3354 = try_lookup_effect_lid env ftv in
      match uu____3354 with
      | None  ->
          let uu____3356 =
            let uu____3357 =
              let uu____3360 = name_not_found ftv in
              (uu____3360, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3357 in
          Prims.raise uu____3356
      | Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp) Prims.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3374 = lookup_qname env lid0 in
        match uu____3374 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3392);
                FStar_Syntax_Syntax.sigrng = uu____3393;
                FStar_Syntax_Syntax.sigqual = quals;_},None
              ),uu____3395)
            ->
            let lid1 =
              let uu____3422 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3422 in
            let uu____3423 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___105_3425  ->
                      match uu___105_3425 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3426 -> false)) in
            if uu____3423
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   if
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                       &&
                       ((FStar_List.length univ_insts) =
                          (Prims.parse_int "1"))
                   then
                     FStar_List.append univ_insts
                       [FStar_Syntax_Syntax.U_zero]
                   else
                     (let uu____3442 =
                        let uu____3443 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3444 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3443 uu____3444 in
                      failwith uu____3442) in
               match (binders, univs1) with
               | ([],uu____3450) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3459,uu____3460::uu____3461::uu____3462) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3465 =
                     let uu____3466 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3467 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3466 uu____3467 in
                   failwith uu____3465
               | uu____3473 ->
                   let uu____3476 =
                     let uu____3479 =
                       let uu____3480 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3480) in
                     inst_tscheme_with uu____3479 insts in
                   (match uu____3476 with
                    | (uu____3488,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3491 =
                          let uu____3492 = FStar_Syntax_Subst.compress t1 in
                          uu____3492.FStar_Syntax_Syntax.n in
                        (match uu____3491 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3522 -> failwith "Impossible")))
        | uu____3526 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3552 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3552 with
        | None  -> None
        | Some (uu____3559,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3564 = find1 l2 in
            (match uu____3564 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3569 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3569 with
        | Some l1 -> l1
        | None  ->
            let uu____3572 = find1 l in
            (match uu____3572 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3584 = lookup_qname env l1 in
      match uu____3584 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3596;
              FStar_Syntax_Syntax.sigrng = uu____3597;
              FStar_Syntax_Syntax.sigqual = q;_},uu____3599),uu____3600)
          -> q
      | uu____3625 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3648 =
          let uu____3649 =
            let uu____3650 = FStar_Util.string_of_int i in
            let uu____3651 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3650 uu____3651 in
          failwith uu____3649 in
        let uu____3652 = lookup_datacon env lid in
        match uu____3652 with
        | (uu____3655,t) ->
            let uu____3657 =
              let uu____3658 = FStar_Syntax_Subst.compress t in
              uu____3658.FStar_Syntax_Syntax.n in
            (match uu____3657 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3662) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3683 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i in
                    FStar_All.pipe_right uu____3683 Prims.fst)
             | uu____3688 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3695 = lookup_qname env l in
      match uu____3695 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3706,uu____3707,uu____3708);
              FStar_Syntax_Syntax.sigrng = uu____3709;
              FStar_Syntax_Syntax.sigqual = quals;_},uu____3711),uu____3712)
          ->
          FStar_Util.for_some
            (fun uu___106_3737  ->
               match uu___106_3737 with
               | FStar_Syntax_Syntax.Projector uu____3738 -> true
               | uu____3741 -> false) quals
      | uu____3742 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3759 = lookup_qname env lid in
      match uu____3759 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3770,uu____3771,uu____3772,uu____3773,uu____3774,uu____3775);
              FStar_Syntax_Syntax.sigrng = uu____3776;
              FStar_Syntax_Syntax.sigqual = uu____3777;_},uu____3778),uu____3779)
          -> true
      | uu____3806 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3823 = lookup_qname env lid in
      match uu____3823 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3834,uu____3835,uu____3836,uu____3837,uu____3838,uu____3839);
              FStar_Syntax_Syntax.sigrng = uu____3840;
              FStar_Syntax_Syntax.sigqual = quals;_},uu____3842),uu____3843)
          ->
          FStar_Util.for_some
            (fun uu___107_3872  ->
               match uu___107_3872 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3875 -> false) quals
      | uu____3876 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3893 = lookup_qname env lid in
      match uu____3893 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3904,uu____3905,uu____3906);
              FStar_Syntax_Syntax.sigrng = uu____3907;
              FStar_Syntax_Syntax.sigqual = quals;_},uu____3909),uu____3910)
          ->
          FStar_Util.for_some
            (fun uu___108_3939  ->
               match uu___108_3939 with
               | FStar_Syntax_Syntax.Action uu____3940 -> true
               | uu____3941 -> false) quals
      | uu____3942 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Syntax_Const.op_Eq;
    FStar_Syntax_Const.op_notEq;
    FStar_Syntax_Const.op_LT;
    FStar_Syntax_Const.op_LTE;
    FStar_Syntax_Const.op_GT;
    FStar_Syntax_Const.op_GTE;
    FStar_Syntax_Const.op_Subtraction;
    FStar_Syntax_Const.op_Minus;
    FStar_Syntax_Const.op_Addition;
    FStar_Syntax_Const.op_Multiply;
    FStar_Syntax_Const.op_Division;
    FStar_Syntax_Const.op_Modulus;
    FStar_Syntax_Const.op_And;
    FStar_Syntax_Const.op_Or;
    FStar_Syntax_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____3961 =
        let uu____3962 = FStar_Syntax_Util.un_uinst head1 in
        uu____3962.FStar_Syntax_Syntax.n in
      match uu____3961 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3966 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____4004 -> Some false
        | FStar_Util.Inr (se,uu____4013) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4022 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigqual)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4026 -> Some true
             | uu____4035 -> Some false) in
      let uu____4036 =
        let uu____4038 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4038 mapper in
      match uu____4036 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4065 = lookup_qname env lid in
      match uu____4065 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4076,uu____4077,tps,uu____4079,uu____4080,uu____4081);
              FStar_Syntax_Syntax.sigrng = uu____4082;
              FStar_Syntax_Syntax.sigqual = uu____4083;_},uu____4084),uu____4085)
          -> FStar_List.length tps
      | uu____4117 ->
          let uu____4128 =
            let uu____4129 =
              let uu____4132 = name_not_found lid in
              (uu____4132, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4129 in
          Prims.raise uu____4128
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4154  ->
              match uu____4154 with
              | (d,uu____4159) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4168 = effect_decl_opt env l in
      match uu____4168 with
      | None  ->
          let uu____4176 =
            let uu____4177 =
              let uu____4180 = name_not_found l in
              (uu____4180, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4177 in
          Prims.raise uu____4176
      | Some md -> Prims.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term = (Some (fun t  -> fun wp  -> fun e  -> e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident* mlift* mlift)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid))
          then
            (FStar_Syntax_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____4223 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4247  ->
                       match uu____4247 with
                       | (m1,m2,uu____4255,uu____4256,uu____4257) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4223 with
             | None  ->
                 let uu____4266 =
                   let uu____4267 =
                     let uu____4270 =
                       let uu____4271 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4272 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4271
                         uu____4272 in
                     (uu____4270, (env.range)) in
                   FStar_Errors.Error uu____4267 in
                 Prims.raise uu____4266
             | Some (uu____4276,uu____4277,m3,j1,j2) -> (m3, j1, j2))
let monad_leq:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> edge Prims.option =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))
        then Some { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux decls m =
  let uu____4324 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4336  ->
            match uu____4336 with
            | (d,uu____4340) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4324 with
  | None  ->
      let uu____4347 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4347
  | Some (md,_q) ->
      let uu____4356 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4356 with
       | (uu____4363,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4371)::(wp,uu____4373)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4395 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid
          then FStar_Syntax_Syntax.mk_Total' res_t (Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Syntax_Const.effect_GTot_lid
            then FStar_Syntax_Syntax.mk_GTotal' res_t (Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____4431 = get_range env in
                 let uu____4432 =
                   let uu____4435 =
                     let uu____4436 =
                       let uu____4446 =
                         let uu____4448 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4448] in
                       (null_wp, uu____4446) in
                     FStar_Syntax_Syntax.Tm_app uu____4436 in
                   FStar_Syntax_Syntax.mk uu____4435 in
                 uu____4432 None uu____4431 in
               let uu____4458 =
                 let uu____4459 =
                   let uu____4465 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4465] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4459;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4458)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___119_4474 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigqual)) ::
                ((env.effects).decls));
              order = (uu___119_4474.order);
              joins = (uu___119_4474.joins)
            } in
          let uu___120_4479 = env in
          {
            solver = (uu___120_4479.solver);
            range = (uu___120_4479.range);
            curmodule = (uu___120_4479.curmodule);
            gamma = (uu___120_4479.gamma);
            gamma_cache = (uu___120_4479.gamma_cache);
            modules = (uu___120_4479.modules);
            expected_typ = (uu___120_4479.expected_typ);
            sigtab = (uu___120_4479.sigtab);
            is_pattern = (uu___120_4479.is_pattern);
            instantiate_imp = (uu___120_4479.instantiate_imp);
            effects;
            generalize = (uu___120_4479.generalize);
            letrecs = (uu___120_4479.letrecs);
            top_level = (uu___120_4479.top_level);
            check_uvars = (uu___120_4479.check_uvars);
            use_eq = (uu___120_4479.use_eq);
            is_iface = (uu___120_4479.is_iface);
            admit = (uu___120_4479.admit);
            lax = (uu___120_4479.lax);
            lax_universes = (uu___120_4479.lax_universes);
            type_of = (uu___120_4479.type_of);
            universe_of = (uu___120_4479.universe_of);
            use_bv_sorts = (uu___120_4479.use_bv_sorts);
            qname_and_index = (uu___120_4479.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4496 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4496 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4575 = (e1.mlift).mlift_wp t wp in
                              let uu____4576 = l1 t wp e in
                              l2 t uu____4575 uu____4576))
                | uu____4577 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4612 = inst_tscheme lift_t in
            match uu____4612 with
            | (uu____4617,lift_t1) ->
                let uu____4619 =
                  let uu____4622 =
                    let uu____4623 =
                      let uu____4633 =
                        let uu____4635 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4636 =
                          let uu____4638 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4638] in
                        uu____4635 :: uu____4636 in
                      (lift_t1, uu____4633) in
                    FStar_Syntax_Syntax.Tm_app uu____4623 in
                  FStar_Syntax_Syntax.mk uu____4622 in
                uu____4619 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4683 = inst_tscheme lift_t in
            match uu____4683 with
            | (uu____4688,lift_t1) ->
                let uu____4690 =
                  let uu____4693 =
                    let uu____4694 =
                      let uu____4704 =
                        let uu____4706 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4707 =
                          let uu____4709 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4710 =
                            let uu____4712 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4712] in
                          uu____4709 :: uu____4710 in
                        uu____4706 :: uu____4707 in
                      (lift_t1, uu____4704) in
                    FStar_Syntax_Syntax.Tm_app uu____4694 in
                  FStar_Syntax_Syntax.mk uu____4693 in
                uu____4690 None e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____4753 =
                let uu____4754 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4754
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4753 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4758 =
              let uu____4759 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4759 in
            let uu____4760 =
              let uu____4761 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4776 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4776) in
              FStar_Util.dflt "none" uu____4761 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4758
              uu____4760 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4789  ->
                    match uu____4789 with
                    | (e,uu____4794) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4807 =
            match uu____4807 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_28  -> Some _0_28)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____4832 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____4844 =
                                       let uu____4849 =
                                         find_edge order1 (i, k) in
                                       let uu____4851 =
                                         find_edge order1 (k, j) in
                                       (uu____4849, uu____4851) in
                                     match uu____4844 with
                                     | (Some e1,Some e2) ->
                                         let uu____4860 = compose_edges e1 e2 in
                                         [uu____4860]
                                     | uu____4861 -> []))))) in
              FStar_List.append order1 uu____4832 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____4876 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4877 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4877
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4876
                   then
                     let uu____4880 =
                       let uu____4881 =
                         let uu____4884 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4885 = get_range env in
                         (uu____4884, uu____4885) in
                       FStar_Errors.Error uu____4881 in
                     Prims.raise uu____4880
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then Some (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____4948 =
                                              let uu____4953 =
                                                find_edge order2 (i, k) in
                                              let uu____4955 =
                                                find_edge order2 (j, k) in
                                              (uu____4953, uu____4955) in
                                            match uu____4948 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____4978,uu____4979)
                                                     ->
                                                     let uu____4983 =
                                                       let uu____4986 =
                                                         let uu____4987 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____4987 in
                                                       let uu____4989 =
                                                         let uu____4990 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____4990 in
                                                       (uu____4986,
                                                         uu____4989) in
                                                     (match uu____4983 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          Some (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____5009 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___121_5048 = env.effects in
              { decls = (uu___121_5048.decls); order = order2; joins } in
            let uu___122_5049 = env in
            {
              solver = (uu___122_5049.solver);
              range = (uu___122_5049.range);
              curmodule = (uu___122_5049.curmodule);
              gamma = (uu___122_5049.gamma);
              gamma_cache = (uu___122_5049.gamma_cache);
              modules = (uu___122_5049.modules);
              expected_typ = (uu___122_5049.expected_typ);
              sigtab = (uu___122_5049.sigtab);
              is_pattern = (uu___122_5049.is_pattern);
              instantiate_imp = (uu___122_5049.instantiate_imp);
              effects;
              generalize = (uu___122_5049.generalize);
              letrecs = (uu___122_5049.letrecs);
              top_level = (uu___122_5049.top_level);
              check_uvars = (uu___122_5049.check_uvars);
              use_eq = (uu___122_5049.use_eq);
              is_iface = (uu___122_5049.is_iface);
              admit = (uu___122_5049.admit);
              lax = (uu___122_5049.lax);
              lax_universes = (uu___122_5049.lax_universes);
              type_of = (uu___122_5049.type_of);
              universe_of = (uu___122_5049.universe_of);
              use_bv_sorts = (uu___122_5049.use_bv_sorts);
              qname_and_index = (uu___122_5049.qname_and_index)
            }))
      | uu____5050 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____5072 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5080 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5080 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5090 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5090 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5107 =
                     let uu____5108 =
                       let uu____5111 =
                         let uu____5112 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5118 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5126 =
                           let uu____5127 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5127 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5112 uu____5118 uu____5126 in
                       (uu____5111, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5108 in
                   Prims.raise uu____5107)
                else ();
                (let inst1 =
                   let uu____5131 =
                     let uu____5137 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5137 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5144  ->
                        fun uu____5145  ->
                          match (uu____5144, uu____5145) with
                          | ((x,uu____5159),(t,uu____5161)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5131 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5176 =
                     let uu___123_5177 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___123_5177.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___123_5177.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___123_5177.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___123_5177.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5176
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5207 =
    let uu____5212 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5212 in
  match uu____5207 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5228 =
        only_reifiable &&
          (let uu____5229 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5229) in
      if uu____5228
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5242 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5244 =
               let uu____5253 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5253) in
             (match uu____5244 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5287 =
                    let uu____5290 = get_range env in
                    let uu____5291 =
                      let uu____5294 =
                        let uu____5295 =
                          let uu____5305 =
                            let uu____5307 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5307; wp] in
                          (repr, uu____5305) in
                        FStar_Syntax_Syntax.Tm_app uu____5295 in
                      FStar_Syntax_Syntax.mk uu____5294 in
                    uu____5291 None uu____5290 in
                  Some uu____5287))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax Prims.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____5351 =
            let uu____5352 =
              let uu____5355 =
                let uu____5356 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5356 in
              let uu____5357 = get_range env in (uu____5355, uu____5357) in
            FStar_Errors.Error uu____5352 in
          Prims.raise uu____5351 in
        let uu____5358 = effect_repr_aux true env c u_c in
        match uu____5358 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable:
  env ->
    (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either -> Prims.bool
  =
  fun env  ->
    fun c  ->
      let effect_lid =
        match c with
        | FStar_Util.Inl lc -> lc.FStar_Syntax_Syntax.eff_name
        | FStar_Util.Inr (eff_name,uu____5390) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5403 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5410 =
        let uu____5411 = FStar_Syntax_Subst.compress t in
        uu____5411.FStar_Syntax_Syntax.n in
      match uu____5410 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5414,c) ->
          is_reifiable_comp env c
      | uu____5426 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5451 = push1 x rest1 in local :: uu____5451 in
      let uu___124_5453 = env in
      let uu____5454 = push1 s env.gamma in
      {
        solver = (uu___124_5453.solver);
        range = (uu___124_5453.range);
        curmodule = (uu___124_5453.curmodule);
        gamma = uu____5454;
        gamma_cache = (uu___124_5453.gamma_cache);
        modules = (uu___124_5453.modules);
        expected_typ = (uu___124_5453.expected_typ);
        sigtab = (uu___124_5453.sigtab);
        is_pattern = (uu___124_5453.is_pattern);
        instantiate_imp = (uu___124_5453.instantiate_imp);
        effects = (uu___124_5453.effects);
        generalize = (uu___124_5453.generalize);
        letrecs = (uu___124_5453.letrecs);
        top_level = (uu___124_5453.top_level);
        check_uvars = (uu___124_5453.check_uvars);
        use_eq = (uu___124_5453.use_eq);
        is_iface = (uu___124_5453.is_iface);
        admit = (uu___124_5453.admit);
        lax = (uu___124_5453.lax);
        lax_universes = (uu___124_5453.lax_universes);
        type_of = (uu___124_5453.type_of);
        universe_of = (uu___124_5453.universe_of);
        use_bv_sorts = (uu___124_5453.use_bv_sorts);
        qname_and_index = (uu___124_5453.qname_and_index)
      }
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___125_5481 = env in
      {
        solver = (uu___125_5481.solver);
        range = (uu___125_5481.range);
        curmodule = (uu___125_5481.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___125_5481.gamma_cache);
        modules = (uu___125_5481.modules);
        expected_typ = (uu___125_5481.expected_typ);
        sigtab = (uu___125_5481.sigtab);
        is_pattern = (uu___125_5481.is_pattern);
        instantiate_imp = (uu___125_5481.instantiate_imp);
        effects = (uu___125_5481.effects);
        generalize = (uu___125_5481.generalize);
        letrecs = (uu___125_5481.letrecs);
        top_level = (uu___125_5481.top_level);
        check_uvars = (uu___125_5481.check_uvars);
        use_eq = (uu___125_5481.use_eq);
        is_iface = (uu___125_5481.is_iface);
        admit = (uu___125_5481.admit);
        lax = (uu___125_5481.lax);
        lax_universes = (uu___125_5481.lax_universes);
        type_of = (uu___125_5481.type_of);
        universe_of = (uu___125_5481.universe_of);
        use_bv_sorts = (uu___125_5481.use_bv_sorts);
        qname_and_index = (uu___125_5481.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) Prims.option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___126_5502 = env in
             {
               solver = (uu___126_5502.solver);
               range = (uu___126_5502.range);
               curmodule = (uu___126_5502.curmodule);
               gamma = rest;
               gamma_cache = (uu___126_5502.gamma_cache);
               modules = (uu___126_5502.modules);
               expected_typ = (uu___126_5502.expected_typ);
               sigtab = (uu___126_5502.sigtab);
               is_pattern = (uu___126_5502.is_pattern);
               instantiate_imp = (uu___126_5502.instantiate_imp);
               effects = (uu___126_5502.effects);
               generalize = (uu___126_5502.generalize);
               letrecs = (uu___126_5502.letrecs);
               top_level = (uu___126_5502.top_level);
               check_uvars = (uu___126_5502.check_uvars);
               use_eq = (uu___126_5502.use_eq);
               is_iface = (uu___126_5502.is_iface);
               admit = (uu___126_5502.admit);
               lax = (uu___126_5502.lax);
               lax_universes = (uu___126_5502.lax_universes);
               type_of = (uu___126_5502.type_of);
               universe_of = (uu___126_5502.universe_of);
               use_bv_sorts = (uu___126_5502.use_bv_sorts);
               qname_and_index = (uu___126_5502.qname_and_index)
             }))
    | uu____5503 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5516  ->
             match uu____5516 with | (x,uu____5520) -> push_bv env1 x) env bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___127_5540 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___127_5540.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___127_5540.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (Prims.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___128_5570 = env in
       {
         solver = (uu___128_5570.solver);
         range = (uu___128_5570.range);
         curmodule = (uu___128_5570.curmodule);
         gamma = [];
         gamma_cache = (uu___128_5570.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___128_5570.sigtab);
         is_pattern = (uu___128_5570.is_pattern);
         instantiate_imp = (uu___128_5570.instantiate_imp);
         effects = (uu___128_5570.effects);
         generalize = (uu___128_5570.generalize);
         letrecs = (uu___128_5570.letrecs);
         top_level = (uu___128_5570.top_level);
         check_uvars = (uu___128_5570.check_uvars);
         use_eq = (uu___128_5570.use_eq);
         is_iface = (uu___128_5570.is_iface);
         admit = (uu___128_5570.admit);
         lax = (uu___128_5570.lax);
         lax_universes = (uu___128_5570.lax_universes);
         type_of = (uu___128_5570.type_of);
         universe_of = (uu___128_5570.universe_of);
         use_bv_sorts = (uu___128_5570.use_bv_sorts);
         qname_and_index = (uu___128_5570.qname_and_index)
       })
let push_univ_vars: env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env* FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term
          Prims.list)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____5594 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5594 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5610 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5610)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___129_5620 = env in
      {
        solver = (uu___129_5620.solver);
        range = (uu___129_5620.range);
        curmodule = (uu___129_5620.curmodule);
        gamma = (uu___129_5620.gamma);
        gamma_cache = (uu___129_5620.gamma_cache);
        modules = (uu___129_5620.modules);
        expected_typ = (Some t);
        sigtab = (uu___129_5620.sigtab);
        is_pattern = (uu___129_5620.is_pattern);
        instantiate_imp = (uu___129_5620.instantiate_imp);
        effects = (uu___129_5620.effects);
        generalize = (uu___129_5620.generalize);
        letrecs = (uu___129_5620.letrecs);
        top_level = (uu___129_5620.top_level);
        check_uvars = (uu___129_5620.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5620.is_iface);
        admit = (uu___129_5620.admit);
        lax = (uu___129_5620.lax);
        lax_universes = (uu___129_5620.lax_universes);
        type_of = (uu___129_5620.type_of);
        universe_of = (uu___129_5620.universe_of);
        use_bv_sorts = (uu___129_5620.use_bv_sorts);
        qname_and_index = (uu___129_5620.qname_and_index)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ Prims.option) =
  fun env_  ->
    let uu____5636 = expected_typ env_ in
    ((let uu___130_5639 = env_ in
      {
        solver = (uu___130_5639.solver);
        range = (uu___130_5639.range);
        curmodule = (uu___130_5639.curmodule);
        gamma = (uu___130_5639.gamma);
        gamma_cache = (uu___130_5639.gamma_cache);
        modules = (uu___130_5639.modules);
        expected_typ = None;
        sigtab = (uu___130_5639.sigtab);
        is_pattern = (uu___130_5639.is_pattern);
        instantiate_imp = (uu___130_5639.instantiate_imp);
        effects = (uu___130_5639.effects);
        generalize = (uu___130_5639.generalize);
        letrecs = (uu___130_5639.letrecs);
        top_level = (uu___130_5639.top_level);
        check_uvars = (uu___130_5639.check_uvars);
        use_eq = false;
        is_iface = (uu___130_5639.is_iface);
        admit = (uu___130_5639.admit);
        lax = (uu___130_5639.lax);
        lax_universes = (uu___130_5639.lax_universes);
        type_of = (uu___130_5639.type_of);
        universe_of = (uu___130_5639.universe_of);
        use_bv_sorts = (uu___130_5639.use_bv_sorts);
        qname_and_index = (uu___130_5639.qname_and_index)
      }), uu____5636)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5650 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___109_5654  ->
                    match uu___109_5654 with
                    | Binding_sig (uu____5656,se) -> [se]
                    | uu____5660 -> [])) in
          FStar_All.pipe_right uu____5650 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___131_5665 = env in
       {
         solver = (uu___131_5665.solver);
         range = (uu___131_5665.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___131_5665.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___131_5665.expected_typ);
         sigtab = (uu___131_5665.sigtab);
         is_pattern = (uu___131_5665.is_pattern);
         instantiate_imp = (uu___131_5665.instantiate_imp);
         effects = (uu___131_5665.effects);
         generalize = (uu___131_5665.generalize);
         letrecs = (uu___131_5665.letrecs);
         top_level = (uu___131_5665.top_level);
         check_uvars = (uu___131_5665.check_uvars);
         use_eq = (uu___131_5665.use_eq);
         is_iface = (uu___131_5665.is_iface);
         admit = (uu___131_5665.admit);
         lax = (uu___131_5665.lax);
         lax_universes = (uu___131_5665.lax_universes);
         type_of = (uu___131_5665.type_of);
         universe_of = (uu___131_5665.universe_of);
         use_bv_sorts = (uu___131_5665.use_bv_sorts);
         qname_and_index = (uu___131_5665.qname_and_index)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5715)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5730 =
            let uu____5734 = FStar_Syntax_Free.uvars t in ext out uu____5734 in
          aux uu____5730 tl1
      | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> out in
    aux no_uvs1 env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst _)::tl1|(Binding_univ _)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5790 =
            let uu____5792 = FStar_Syntax_Free.univs t in ext out uu____5792 in
          aux uu____5790 tl1
      | (Binding_sig uu____5794)::uu____5795 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5832)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5842 = FStar_Util.set_add uname out in aux uu____5842 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5856 =
            let uu____5858 = FStar_Syntax_Free.univnames t in
            ext out uu____5858 in
          aux uu____5856 tl1
      | (Binding_sig uu____5860)::uu____5861 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___110_5877  ->
            match uu___110_5877 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5889 =
      let uu____5891 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____5891
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____5889 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____5907 =
      let uu____5908 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___111_5912  ->
                match uu___111_5912 with
                | Binding_var x ->
                    let uu____5914 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____5914
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____5917) ->
                    let uu____5918 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____5918
                | Binding_sig (ls,uu____5920) ->
                    let uu____5923 =
                      let uu____5924 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____5924
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____5923
                | Binding_sig_inst (ls,uu____5930,uu____5931) ->
                    let uu____5934 =
                      let uu____5935 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____5935
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____5934)) in
      FStar_All.pipe_right uu____5908 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____5907 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____5947 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____5947
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____5964  ->
                 fun uu____5965  ->
                   match (uu____5964, uu____5965) with
                   | ((b1,uu____5975),(b2,uu____5977)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___112_6020  ->
             match uu___112_6020 with
             | Binding_sig (lids,uu____6024) -> FStar_List.append lids keys
             | uu____6027 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6029  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6033  -> ());
    push = (fun uu____6034  -> ());
    pop = (fun uu____6035  -> ());
    mark = (fun uu____6036  -> ());
    reset_mark = (fun uu____6037  -> ());
    commit_mark = (fun uu____6038  -> ());
    encode_modul = (fun uu____6039  -> fun uu____6040  -> ());
    encode_sig = (fun uu____6041  -> fun uu____6042  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6049  -> fun uu____6050  -> fun uu____6051  -> ());
    is_trivial = (fun uu____6055  -> fun uu____6056  -> false);
    finish = (fun uu____6057  -> ());
    refresh = (fun uu____6058  -> ())
  }