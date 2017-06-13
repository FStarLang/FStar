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
    match projectee with | Binding_var _0 -> true | uu____34 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____48 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____69 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____90 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____106 -> false
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
    match projectee with | NoDelta  -> true | uu____133 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____137 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____141 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____146 -> false
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
      option;}
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
                                                               option))
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
  expected_typ: FStar_Syntax_Syntax.typ option;
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
  qname_and_index: (FStar_Ident.lident* Prims.int) option;}
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
    (Prims.unit -> Prims.string) option ->
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
      | (NoDelta ,uu____929) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____930,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____931,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____932 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____942 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____950 =
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
          let uu____989 = new_gamma_cache () in
          let uu____991 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____989;
            modules = [];
            expected_typ = None;
            sigtab = uu____991;
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
  fun uu____1034  ->
    let uu____1035 = FStar_ST.read query_indices in
    match uu____1035 with
    | [] -> failwith "Empty query indices!"
    | uu____1049 ->
        let uu____1054 =
          let uu____1059 =
            let uu____1063 = FStar_ST.read query_indices in
            FStar_List.hd uu____1063 in
          let uu____1077 = FStar_ST.read query_indices in uu____1059 ::
            uu____1077 in
        FStar_ST.write query_indices uu____1054
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1099  ->
    let uu____1100 = FStar_ST.read query_indices in
    match uu____1100 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1136  ->
    match uu____1136 with
    | (l,n1) ->
        let uu____1141 = FStar_ST.read query_indices in
        (match uu____1141 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1175 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1185  ->
    let uu____1186 = FStar_ST.read query_indices in FStar_List.hd uu____1186
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1202  ->
    let uu____1203 = FStar_ST.read query_indices in
    match uu____1203 with
    | hd1::uu____1215::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1242 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1256 =
       let uu____1258 = FStar_ST.read stack in env :: uu____1258 in
     FStar_ST.write stack uu____1256);
    (let uu___112_1266 = env in
     let uu____1267 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1269 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1266.solver);
       range = (uu___112_1266.range);
       curmodule = (uu___112_1266.curmodule);
       gamma = (uu___112_1266.gamma);
       gamma_cache = uu____1267;
       modules = (uu___112_1266.modules);
       expected_typ = (uu___112_1266.expected_typ);
       sigtab = uu____1269;
       is_pattern = (uu___112_1266.is_pattern);
       instantiate_imp = (uu___112_1266.instantiate_imp);
       effects = (uu___112_1266.effects);
       generalize = (uu___112_1266.generalize);
       letrecs = (uu___112_1266.letrecs);
       top_level = (uu___112_1266.top_level);
       check_uvars = (uu___112_1266.check_uvars);
       use_eq = (uu___112_1266.use_eq);
       is_iface = (uu___112_1266.is_iface);
       admit = (uu___112_1266.admit);
       lax = (uu___112_1266.lax);
       lax_universes = (uu___112_1266.lax_universes);
       type_of = (uu___112_1266.type_of);
       universe_of = (uu___112_1266.universe_of);
       use_bv_sorts = (uu___112_1266.use_bv_sorts);
       qname_and_index = (uu___112_1266.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1273  ->
    let uu____1274 = FStar_ST.read stack in
    match uu____1274 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1286 -> failwith "Impossible: Too many pops"
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
    (let uu____1318 = pop_stack () in ());
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
        let uu____1337 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1349  ->
                  match uu____1349 with
                  | (m,uu____1353) -> FStar_Ident.lid_equals l m)) in
        (match uu____1337 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1358 = env in
               {
                 solver = (uu___113_1358.solver);
                 range = (uu___113_1358.range);
                 curmodule = (uu___113_1358.curmodule);
                 gamma = (uu___113_1358.gamma);
                 gamma_cache = (uu___113_1358.gamma_cache);
                 modules = (uu___113_1358.modules);
                 expected_typ = (uu___113_1358.expected_typ);
                 sigtab = (uu___113_1358.sigtab);
                 is_pattern = (uu___113_1358.is_pattern);
                 instantiate_imp = (uu___113_1358.instantiate_imp);
                 effects = (uu___113_1358.effects);
                 generalize = (uu___113_1358.generalize);
                 letrecs = (uu___113_1358.letrecs);
                 top_level = (uu___113_1358.top_level);
                 check_uvars = (uu___113_1358.check_uvars);
                 use_eq = (uu___113_1358.use_eq);
                 is_iface = (uu___113_1358.is_iface);
                 admit = (uu___113_1358.admit);
                 lax = (uu___113_1358.lax);
                 lax_universes = (uu___113_1358.lax_universes);
                 type_of = (uu___113_1358.type_of);
                 universe_of = (uu___113_1358.universe_of);
                 use_bv_sorts = (uu___113_1358.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1361,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1367 = env in
               {
                 solver = (uu___114_1367.solver);
                 range = (uu___114_1367.range);
                 curmodule = (uu___114_1367.curmodule);
                 gamma = (uu___114_1367.gamma);
                 gamma_cache = (uu___114_1367.gamma_cache);
                 modules = (uu___114_1367.modules);
                 expected_typ = (uu___114_1367.expected_typ);
                 sigtab = (uu___114_1367.sigtab);
                 is_pattern = (uu___114_1367.is_pattern);
                 instantiate_imp = (uu___114_1367.instantiate_imp);
                 effects = (uu___114_1367.effects);
                 generalize = (uu___114_1367.generalize);
                 letrecs = (uu___114_1367.letrecs);
                 top_level = (uu___114_1367.top_level);
                 check_uvars = (uu___114_1367.check_uvars);
                 use_eq = (uu___114_1367.use_eq);
                 is_iface = (uu___114_1367.is_iface);
                 admit = (uu___114_1367.admit);
                 lax = (uu___114_1367.lax);
                 lax_universes = (uu___114_1367.lax_universes);
                 type_of = (uu___114_1367.type_of);
                 universe_of = (uu___114_1367.universe_of);
                 use_bv_sorts = (uu___114_1367.use_bv_sorts);
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
        (let uu___115_1383 = e in
         {
           solver = (uu___115_1383.solver);
           range = r;
           curmodule = (uu___115_1383.curmodule);
           gamma = (uu___115_1383.gamma);
           gamma_cache = (uu___115_1383.gamma_cache);
           modules = (uu___115_1383.modules);
           expected_typ = (uu___115_1383.expected_typ);
           sigtab = (uu___115_1383.sigtab);
           is_pattern = (uu___115_1383.is_pattern);
           instantiate_imp = (uu___115_1383.instantiate_imp);
           effects = (uu___115_1383.effects);
           generalize = (uu___115_1383.generalize);
           letrecs = (uu___115_1383.letrecs);
           top_level = (uu___115_1383.top_level);
           check_uvars = (uu___115_1383.check_uvars);
           use_eq = (uu___115_1383.use_eq);
           is_iface = (uu___115_1383.is_iface);
           admit = (uu___115_1383.admit);
           lax = (uu___115_1383.lax);
           lax_universes = (uu___115_1383.lax_universes);
           type_of = (uu___115_1383.type_of);
           universe_of = (uu___115_1383.universe_of);
           use_bv_sorts = (uu___115_1383.use_bv_sorts);
           qname_and_index = (uu___115_1383.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1400 = env in
      {
        solver = (uu___116_1400.solver);
        range = (uu___116_1400.range);
        curmodule = lid;
        gamma = (uu___116_1400.gamma);
        gamma_cache = (uu___116_1400.gamma_cache);
        modules = (uu___116_1400.modules);
        expected_typ = (uu___116_1400.expected_typ);
        sigtab = (uu___116_1400.sigtab);
        is_pattern = (uu___116_1400.is_pattern);
        instantiate_imp = (uu___116_1400.instantiate_imp);
        effects = (uu___116_1400.effects);
        generalize = (uu___116_1400.generalize);
        letrecs = (uu___116_1400.letrecs);
        top_level = (uu___116_1400.top_level);
        check_uvars = (uu___116_1400.check_uvars);
        use_eq = (uu___116_1400.use_eq);
        is_iface = (uu___116_1400.is_iface);
        admit = (uu___116_1400.admit);
        lax = (uu___116_1400.lax);
        lax_universes = (uu___116_1400.lax_universes);
        type_of = (uu___116_1400.type_of);
        universe_of = (uu___116_1400.universe_of);
        use_bv_sorts = (uu___116_1400.use_bv_sorts);
        qname_and_index = (uu___116_1400.qname_and_index)
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
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1422 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1422
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1425  ->
    let uu____1426 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1426
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1450) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1466 = FStar_Syntax_Subst.subst vs t in (us, uu____1466)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1471  ->
    match uu___100_1471 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1485  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1495 = inst_tscheme t in
      match uu____1495 with
      | (us,t1) ->
          let uu____1502 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1502)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1514  ->
          match uu____1514 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1528 =
                         let uu____1529 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1532 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1535 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1536 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1529 uu____1532 uu____1535 uu____1536 in
                       failwith uu____1528)
                    else ();
                    (let uu____1538 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1538))
               | uu____1542 ->
                   let uu____1543 =
                     let uu____1544 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1544 in
                   failwith uu____1543)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1548 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1552 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1556 -> false
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
             | ([],uu____1582) -> Maybe
             | (uu____1586,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1598 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                                   FStar_Syntax_Syntax.universes
                                                                   option))
        FStar_Util.either* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t in
      let found =
        if cur_mod <> No
        then
          let uu____1658 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1658 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1679  ->
                   match uu___101_1679 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1702 =
                           let uu____1712 =
                             let uu____1720 = inst_tscheme t in
                             FStar_Util.Inl uu____1720 in
                           (uu____1712, (FStar_Ident.range_of_lid l)) in
                         Some uu____1702
                       else None
                   | Binding_sig
                       (uu____1754,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1756);
                                     FStar_Syntax_Syntax.sigrng = uu____1757;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1758;
                                     FStar_Syntax_Syntax.sigmeta = uu____1759;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1768 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1768
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1795 ->
                             Some t
                         | uu____1799 -> cache t in
                       let uu____1800 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1800 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1840 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1840 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1884 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1926 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1926
         then
           let uu____1937 = find_in_sigtab env lid in
           match uu____1937 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2003) ->
          add_sigelts env ses
      | uu____2008 ->
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
            | uu____2017 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Range.range) option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___102_2035  ->
           match uu___102_2035 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2048 -> None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
        FStar_Range.range) option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2069,lb::[]),uu____2071,uu____2072) ->
          let uu____2081 =
            let uu____2086 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2092 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2086, uu____2092) in
          Some uu____2081
      | FStar_Syntax_Syntax.Sig_let ((uu____2099,lbs),uu____2101,uu____2102)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2122 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2129 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2129
                   then
                     let uu____2135 =
                       let uu____2140 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2146 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2140, uu____2146) in
                     Some uu____2135
                   else None)
      | uu____2158 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2177 =
          let uu____2182 =
            let uu____2185 =
              let uu____2186 =
                let uu____2189 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2189 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2186) in
            inst_tscheme uu____2185 in
          (uu____2182, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2177
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2203,uu____2204) ->
        let uu____2207 =
          let uu____2212 =
            let uu____2215 =
              let uu____2216 =
                let uu____2219 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2219 in
              (us, uu____2216) in
            inst_tscheme uu____2215 in
          (uu____2212, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2207
    | uu____2230 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2265 =
        match uu____2265 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2315,uvs,t,uu____2318,uu____2319,uu____2320);
                    FStar_Syntax_Syntax.sigrng = uu____2321;
                    FStar_Syntax_Syntax.sigquals = uu____2322;
                    FStar_Syntax_Syntax.sigmeta = uu____2323;_},None
                  )
                 ->
                 let uu____2333 =
                   let uu____2338 = inst_tscheme (uvs, t) in
                   (uu____2338, rng) in
                 Some uu____2333
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2350;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2352;_},None
                  )
                 ->
                 let uu____2360 =
                   let uu____2361 = in_cur_mod env l in uu____2361 = Yes in
                 if uu____2360
                 then
                   let uu____2367 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2367
                    then
                      let uu____2374 =
                        let uu____2379 = inst_tscheme (uvs, t) in
                        (uu____2379, rng) in
                      Some uu____2374
                    else None)
                 else
                   (let uu____2394 =
                      let uu____2399 = inst_tscheme (uvs, t) in
                      (uu____2399, rng) in
                    Some uu____2394)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2412,uu____2413);
                    FStar_Syntax_Syntax.sigrng = uu____2414;
                    FStar_Syntax_Syntax.sigquals = uu____2415;
                    FStar_Syntax_Syntax.sigmeta = uu____2416;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2435 =
                        let uu____2440 = inst_tscheme (uvs, k) in
                        (uu____2440, rng) in
                      Some uu____2435
                  | uu____2449 ->
                      let uu____2450 =
                        let uu____2455 =
                          let uu____2458 =
                            let uu____2459 =
                              let uu____2462 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2462 in
                            (uvs, uu____2459) in
                          inst_tscheme uu____2458 in
                        (uu____2455, rng) in
                      Some uu____2450)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2477,uu____2478);
                    FStar_Syntax_Syntax.sigrng = uu____2479;
                    FStar_Syntax_Syntax.sigquals = uu____2480;
                    FStar_Syntax_Syntax.sigmeta = uu____2481;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2501 =
                        let uu____2506 = inst_tscheme_with (uvs, k) us in
                        (uu____2506, rng) in
                      Some uu____2501
                  | uu____2515 ->
                      let uu____2516 =
                        let uu____2521 =
                          let uu____2524 =
                            let uu____2525 =
                              let uu____2528 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2528 in
                            (uvs, uu____2525) in
                          inst_tscheme_with uu____2524 us in
                        (uu____2521, rng) in
                      Some uu____2516)
             | FStar_Util.Inr se ->
                 let uu____2548 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2559;
                        FStar_Syntax_Syntax.sigrng = uu____2560;
                        FStar_Syntax_Syntax.sigquals = uu____2561;
                        FStar_Syntax_Syntax.sigmeta = uu____2562;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2571 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2548
                   (FStar_Util.map_option
                      (fun uu____2594  ->
                         match uu____2594 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2611 =
        let uu____2617 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2617 mapper in
      match uu____2611 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2669 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2669.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2669.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2669.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2690 = lookup_qname env l in
      match uu____2690 with | None  -> false | Some uu____2710 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2738 = try_lookup_bv env bv in
      match uu____2738 with
      | None  ->
          let uu____2746 =
            let uu____2747 =
              let uu____2750 = variable_not_found bv in (uu____2750, bvr) in
            FStar_Errors.Error uu____2747 in
          raise uu____2746
      | Some (t,r) ->
          let uu____2757 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2758 = FStar_Range.set_use_range r bvr in
          (uu____2757, uu____2758)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2770 = try_lookup_lid_aux env l in
      match uu____2770 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2812 =
            let uu____2817 =
              let uu____2820 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2820) in
            (uu____2817, r1) in
          Some uu____2812
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2837 = try_lookup_lid env l in
      match uu____2837 with
      | None  ->
          let uu____2851 =
            let uu____2852 =
              let uu____2855 = name_not_found l in
              (uu____2855, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2852 in
          raise uu____2851
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2876  ->
              match uu___103_2876 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2878 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2889 = lookup_qname env lid in
      match uu____2889 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2904,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2907;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2909;_},None
            ),uu____2910)
          ->
          let uu____2934 =
            let uu____2940 =
              let uu____2943 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2943) in
            (uu____2940, q) in
          Some uu____2934
      | uu____2952 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2974 = lookup_qname env lid in
      match uu____2974 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2987,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2990;
              FStar_Syntax_Syntax.sigquals = uu____2991;
              FStar_Syntax_Syntax.sigmeta = uu____2992;_},None
            ),uu____2993)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3017 ->
          let uu____3028 =
            let uu____3029 =
              let uu____3032 = name_not_found lid in
              (uu____3032, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3029 in
          raise uu____3028
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3043 = lookup_qname env lid in
      match uu____3043 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3056,uvs,t,uu____3059,uu____3060,uu____3061);
              FStar_Syntax_Syntax.sigrng = uu____3062;
              FStar_Syntax_Syntax.sigquals = uu____3063;
              FStar_Syntax_Syntax.sigmeta = uu____3064;_},None
            ),uu____3065)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3091 ->
          let uu____3102 =
            let uu____3103 =
              let uu____3106 = name_not_found lid in
              (uu____3106, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3103 in
          raise uu____3102
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3118 = lookup_qname env lid in
      match uu____3118 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3132,uu____3133,uu____3134,uu____3135,uu____3136,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3138;
              FStar_Syntax_Syntax.sigquals = uu____3139;
              FStar_Syntax_Syntax.sigmeta = uu____3140;_},uu____3141),uu____3142)
          -> (true, dcs)
      | uu____3172 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3190 = lookup_qname env lid in
      match uu____3190 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3201,uu____3202,uu____3203,l,uu____3205,uu____3206);
              FStar_Syntax_Syntax.sigrng = uu____3207;
              FStar_Syntax_Syntax.sigquals = uu____3208;
              FStar_Syntax_Syntax.sigmeta = uu____3209;_},uu____3210),uu____3211)
          -> l
      | uu____3238 ->
          let uu____3249 =
            let uu____3250 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3250 in
          failwith uu____3249
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term) option
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
        let uu____3274 = lookup_qname env lid in
        match uu____3274 with
        | Some (FStar_Util.Inr (se,None ),uu____3289) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3315,lbs),uu____3317,uu____3318) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3335 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3335
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3356 -> None)
        | uu____3359 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3380 = lookup_qname env ftv in
      match uu____3380 with
      | Some (FStar_Util.Inr (se,None ),uu____3393) ->
          let uu____3416 = effect_signature se in
          (match uu____3416 with
           | None  -> None
           | Some ((uu____3427,t),r) ->
               let uu____3436 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3436)
      | uu____3437 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3454 = try_lookup_effect_lid env ftv in
      match uu____3454 with
      | None  ->
          let uu____3456 =
            let uu____3457 =
              let uu____3460 = name_not_found ftv in
              (uu____3460, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3457 in
          raise uu____3456
      | Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp) option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3474 = lookup_qname env lid0 in
        match uu____3474 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3492);
                FStar_Syntax_Syntax.sigrng = uu____3493;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3495;_},None
              ),uu____3496)
            ->
            let lid1 =
              let uu____3523 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3523 in
            let uu____3524 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3526  ->
                      match uu___104_3526 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3527 -> false)) in
            if uu____3524
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3540 =
                      let uu____3541 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3542 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3541 uu____3542 in
                    failwith uu____3540) in
               match (binders, univs1) with
               | ([],uu____3548) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3557,uu____3558::uu____3559::uu____3560) ->
                   let uu____3563 =
                     let uu____3564 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3565 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3564 uu____3565 in
                   failwith uu____3563
               | uu____3571 ->
                   let uu____3574 =
                     let uu____3577 =
                       let uu____3578 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3578) in
                     inst_tscheme_with uu____3577 insts in
                   (match uu____3574 with
                    | (uu____3586,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3589 =
                          let uu____3590 = FStar_Syntax_Subst.compress t1 in
                          uu____3590.FStar_Syntax_Syntax.n in
                        (match uu____3589 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3620 -> failwith "Impossible")))
        | uu____3624 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3650 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3650 with
        | None  -> None
        | Some (uu____3657,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3662 = find1 l2 in
            (match uu____3662 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3667 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3667 with
        | Some l1 -> l1
        | None  ->
            let uu____3670 = find1 l in
            (match uu____3670 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3682 = lookup_qname env l1 in
      match uu____3682 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3694;
              FStar_Syntax_Syntax.sigrng = uu____3695;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3697;_},uu____3698),uu____3699)
          -> q
      | uu____3724 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3747 =
          let uu____3748 =
            let uu____3749 = FStar_Util.string_of_int i in
            let uu____3750 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3749 uu____3750 in
          failwith uu____3748 in
        let uu____3751 = lookup_datacon env lid in
        match uu____3751 with
        | (uu____3754,t) ->
            let uu____3756 =
              let uu____3757 = FStar_Syntax_Subst.compress t in
              uu____3757.FStar_Syntax_Syntax.n in
            (match uu____3756 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3761) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3782 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3782 FStar_Pervasives.fst)
             | uu____3787 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3794 = lookup_qname env l in
      match uu____3794 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3805,uu____3806,uu____3807);
              FStar_Syntax_Syntax.sigrng = uu____3808;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3810;_},uu____3811),uu____3812)
          ->
          FStar_Util.for_some
            (fun uu___105_3837  ->
               match uu___105_3837 with
               | FStar_Syntax_Syntax.Projector uu____3838 -> true
               | uu____3841 -> false) quals
      | uu____3842 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3859 = lookup_qname env lid in
      match uu____3859 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3870,uu____3871,uu____3872,uu____3873,uu____3874,uu____3875);
              FStar_Syntax_Syntax.sigrng = uu____3876;
              FStar_Syntax_Syntax.sigquals = uu____3877;
              FStar_Syntax_Syntax.sigmeta = uu____3878;_},uu____3879),uu____3880)
          -> true
      | uu____3907 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3924 = lookup_qname env lid in
      match uu____3924 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3935,uu____3936,uu____3937,uu____3938,uu____3939,uu____3940);
              FStar_Syntax_Syntax.sigrng = uu____3941;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3943;_},uu____3944),uu____3945)
          ->
          FStar_Util.for_some
            (fun uu___106_3974  ->
               match uu___106_3974 with
               | FStar_Syntax_Syntax.RecordType uu____3975 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3980 -> true
               | uu____3985 -> false) quals
      | uu____3986 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4003 = lookup_qname env lid in
      match uu____4003 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4014,uu____4015,uu____4016);
              FStar_Syntax_Syntax.sigrng = uu____4017;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4019;_},uu____4020),uu____4021)
          ->
          FStar_Util.for_some
            (fun uu___107_4050  ->
               match uu___107_4050 with
               | FStar_Syntax_Syntax.Action uu____4051 -> true
               | uu____4052 -> false) quals
      | uu____4053 -> false
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
      let uu____4072 =
        let uu____4073 = FStar_Syntax_Util.un_uinst head1 in
        uu____4073.FStar_Syntax_Syntax.n in
      match uu____4072 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4077 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4115 -> Some false
        | FStar_Util.Inr (se,uu____4124) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4133 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4137 -> Some true
             | uu____4146 -> Some false) in
      let uu____4147 =
        let uu____4149 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4149 mapper in
      match uu____4147 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4176 = lookup_qname env lid in
      match uu____4176 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4187,uu____4188,tps,uu____4190,uu____4191,uu____4192);
              FStar_Syntax_Syntax.sigrng = uu____4193;
              FStar_Syntax_Syntax.sigquals = uu____4194;
              FStar_Syntax_Syntax.sigmeta = uu____4195;_},uu____4196),uu____4197)
          -> FStar_List.length tps
      | uu____4229 ->
          let uu____4240 =
            let uu____4241 =
              let uu____4244 = name_not_found lid in
              (uu____4244, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4241 in
          raise uu____4240
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4266  ->
              match uu____4266 with
              | (d,uu____4271) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4280 = effect_decl_opt env l in
      match uu____4280 with
      | None  ->
          let uu____4288 =
            let uu____4289 =
              let uu____4292 = name_not_found l in
              (uu____4292, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4289 in
          raise uu____4288
      | Some md -> fst md
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
            (let uu____4335 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4359  ->
                       match uu____4359 with
                       | (m1,m2,uu____4367,uu____4368,uu____4369) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4335 with
             | None  ->
                 let uu____4378 =
                   let uu____4379 =
                     let uu____4382 =
                       let uu____4383 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4384 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4383
                         uu____4384 in
                     (uu____4382, (env.range)) in
                   FStar_Errors.Error uu____4379 in
                 raise uu____4378
             | Some (uu____4388,uu____4389,m3,j1,j2) -> (m3, j1, j2))
let monad_leq: env -> FStar_Ident.lident -> FStar_Ident.lident -> edge option
  =
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
  let uu____4436 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4448  ->
            match uu____4448 with
            | (d,uu____4452) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4436 with
  | None  ->
      let uu____4459 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4459
  | Some (md,_q) ->
      let uu____4468 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4468 with
       | (uu____4475,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4483)::(wp,uu____4485)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4507 -> failwith "Impossible"))
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
                 let uu____4543 = get_range env in
                 let uu____4544 =
                   let uu____4547 =
                     let uu____4548 =
                       let uu____4558 =
                         let uu____4560 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4560] in
                       (null_wp, uu____4558) in
                     FStar_Syntax_Syntax.Tm_app uu____4548 in
                   FStar_Syntax_Syntax.mk uu____4547 in
                 uu____4544 None uu____4543 in
               let uu____4570 =
                 let uu____4571 =
                   let uu____4577 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4577] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4571;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4570)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4586 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4586.order);
              joins = (uu___118_4586.joins)
            } in
          let uu___119_4591 = env in
          {
            solver = (uu___119_4591.solver);
            range = (uu___119_4591.range);
            curmodule = (uu___119_4591.curmodule);
            gamma = (uu___119_4591.gamma);
            gamma_cache = (uu___119_4591.gamma_cache);
            modules = (uu___119_4591.modules);
            expected_typ = (uu___119_4591.expected_typ);
            sigtab = (uu___119_4591.sigtab);
            is_pattern = (uu___119_4591.is_pattern);
            instantiate_imp = (uu___119_4591.instantiate_imp);
            effects;
            generalize = (uu___119_4591.generalize);
            letrecs = (uu___119_4591.letrecs);
            top_level = (uu___119_4591.top_level);
            check_uvars = (uu___119_4591.check_uvars);
            use_eq = (uu___119_4591.use_eq);
            is_iface = (uu___119_4591.is_iface);
            admit = (uu___119_4591.admit);
            lax = (uu___119_4591.lax);
            lax_universes = (uu___119_4591.lax_universes);
            type_of = (uu___119_4591.type_of);
            universe_of = (uu___119_4591.universe_of);
            use_bv_sorts = (uu___119_4591.use_bv_sorts);
            qname_and_index = (uu___119_4591.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4608 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4608 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4687 = (e1.mlift).mlift_wp t wp in
                              let uu____4688 = l1 t wp e in
                              l2 t uu____4687 uu____4688))
                | uu____4689 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4724 = inst_tscheme lift_t in
            match uu____4724 with
            | (uu____4729,lift_t1) ->
                let uu____4731 =
                  let uu____4734 =
                    let uu____4735 =
                      let uu____4745 =
                        let uu____4747 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4748 =
                          let uu____4750 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4750] in
                        uu____4747 :: uu____4748 in
                      (lift_t1, uu____4745) in
                    FStar_Syntax_Syntax.Tm_app uu____4735 in
                  FStar_Syntax_Syntax.mk uu____4734 in
                uu____4731 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4795 = inst_tscheme lift_t in
            match uu____4795 with
            | (uu____4800,lift_t1) ->
                let uu____4802 =
                  let uu____4805 =
                    let uu____4806 =
                      let uu____4816 =
                        let uu____4818 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4819 =
                          let uu____4821 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4822 =
                            let uu____4824 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4824] in
                          uu____4821 :: uu____4822 in
                        uu____4818 :: uu____4819 in
                      (lift_t1, uu____4816) in
                    FStar_Syntax_Syntax.Tm_app uu____4806 in
                  FStar_Syntax_Syntax.mk uu____4805 in
                uu____4802 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4865 =
                let uu____4866 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4866
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4865 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4870 =
              let uu____4871 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4871 in
            let uu____4872 =
              let uu____4873 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4888 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4888) in
              FStar_Util.dflt "none" uu____4873 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4870
              uu____4872 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4901  ->
                    match uu____4901 with
                    | (e,uu____4906) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4919 =
            match uu____4919 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_29  -> Some _0_29)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____4944 =
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
                                    (let uu____4956 =
                                       let uu____4961 =
                                         find_edge order1 (i, k) in
                                       let uu____4963 =
                                         find_edge order1 (k, j) in
                                       (uu____4961, uu____4963) in
                                     match uu____4956 with
                                     | (Some e1,Some e2) ->
                                         let uu____4972 = compose_edges e1 e2 in
                                         [uu____4972]
                                     | uu____4973 -> []))))) in
              FStar_List.append order1 uu____4944 in
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
                   let uu____4988 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4989 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4989
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4988
                   then
                     let uu____4992 =
                       let uu____4993 =
                         let uu____4996 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4997 = get_range env in
                         (uu____4996, uu____4997) in
                       FStar_Errors.Error uu____4993 in
                     raise uu____4992
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
                                            let uu____5060 =
                                              let uu____5065 =
                                                find_edge order2 (i, k) in
                                              let uu____5067 =
                                                find_edge order2 (j, k) in
                                              (uu____5065, uu____5067) in
                                            match uu____5060 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5090,uu____5091)
                                                     ->
                                                     let uu____5095 =
                                                       let uu____5098 =
                                                         let uu____5099 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5099 in
                                                       let uu____5101 =
                                                         let uu____5102 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5102 in
                                                       (uu____5098,
                                                         uu____5101) in
                                                     (match uu____5095 with
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
                                            | uu____5121 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5160 = env.effects in
              { decls = (uu___120_5160.decls); order = order2; joins } in
            let uu___121_5161 = env in
            {
              solver = (uu___121_5161.solver);
              range = (uu___121_5161.range);
              curmodule = (uu___121_5161.curmodule);
              gamma = (uu___121_5161.gamma);
              gamma_cache = (uu___121_5161.gamma_cache);
              modules = (uu___121_5161.modules);
              expected_typ = (uu___121_5161.expected_typ);
              sigtab = (uu___121_5161.sigtab);
              is_pattern = (uu___121_5161.is_pattern);
              instantiate_imp = (uu___121_5161.instantiate_imp);
              effects;
              generalize = (uu___121_5161.generalize);
              letrecs = (uu___121_5161.letrecs);
              top_level = (uu___121_5161.top_level);
              check_uvars = (uu___121_5161.check_uvars);
              use_eq = (uu___121_5161.use_eq);
              is_iface = (uu___121_5161.is_iface);
              admit = (uu___121_5161.admit);
              lax = (uu___121_5161.lax);
              lax_universes = (uu___121_5161.lax_universes);
              type_of = (uu___121_5161.type_of);
              universe_of = (uu___121_5161.universe_of);
              use_bv_sorts = (uu___121_5161.use_bv_sorts);
              qname_and_index = (uu___121_5161.qname_and_index)
            }))
      | uu____5162 -> env
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
        | uu____5184 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5192 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5192 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5202 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5202 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5219 =
                     let uu____5220 =
                       let uu____5223 =
                         let uu____5224 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5230 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5238 =
                           let uu____5239 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5239 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5224 uu____5230 uu____5238 in
                       (uu____5223, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5220 in
                   raise uu____5219)
                else ();
                (let inst1 =
                   let uu____5243 =
                     let uu____5249 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5249 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5256  ->
                        fun uu____5257  ->
                          match (uu____5256, uu____5257) with
                          | ((x,uu____5271),(t,uu____5273)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5243 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5288 =
                     let uu___122_5289 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5289.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5289.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5289.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5289.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5288
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5319 =
    let uu____5324 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5324 in
  match uu____5319 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5340 =
        only_reifiable &&
          (let uu____5341 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5341) in
      if uu____5340
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5354 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5356 =
               let uu____5365 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5365) in
             (match uu____5356 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5399 =
                    let uu____5402 = get_range env in
                    let uu____5403 =
                      let uu____5406 =
                        let uu____5407 =
                          let uu____5417 =
                            let uu____5419 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5419; wp] in
                          (repr, uu____5417) in
                        FStar_Syntax_Syntax.Tm_app uu____5407 in
                      FStar_Syntax_Syntax.mk uu____5406 in
                    uu____5403 None uu____5402 in
                  Some uu____5399))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax option
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
          let uu____5463 =
            let uu____5464 =
              let uu____5467 =
                let uu____5468 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5468 in
              let uu____5469 = get_range env in (uu____5467, uu____5469) in
            FStar_Errors.Error uu____5464 in
          raise uu____5463 in
        let uu____5470 = effect_repr_aux true env c u_c in
        match uu____5470 with
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
        | FStar_Util.Inr (eff_name,uu____5502) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5515 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5522 =
        let uu____5523 = FStar_Syntax_Subst.compress t in
        uu____5523.FStar_Syntax_Syntax.n in
      match uu____5522 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5526,c) ->
          is_reifiable_comp env c
      | uu____5538 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5556)::uu____5557 -> x :: rest
        | (Binding_sig_inst uu____5562)::uu____5563 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5572 = push1 x rest1 in local :: uu____5572 in
      let uu___123_5574 = env in
      let uu____5575 = push1 s env.gamma in
      {
        solver = (uu___123_5574.solver);
        range = (uu___123_5574.range);
        curmodule = (uu___123_5574.curmodule);
        gamma = uu____5575;
        gamma_cache = (uu___123_5574.gamma_cache);
        modules = (uu___123_5574.modules);
        expected_typ = (uu___123_5574.expected_typ);
        sigtab = (uu___123_5574.sigtab);
        is_pattern = (uu___123_5574.is_pattern);
        instantiate_imp = (uu___123_5574.instantiate_imp);
        effects = (uu___123_5574.effects);
        generalize = (uu___123_5574.generalize);
        letrecs = (uu___123_5574.letrecs);
        top_level = (uu___123_5574.top_level);
        check_uvars = (uu___123_5574.check_uvars);
        use_eq = (uu___123_5574.use_eq);
        is_iface = (uu___123_5574.is_iface);
        admit = (uu___123_5574.admit);
        lax = (uu___123_5574.lax);
        lax_universes = (uu___123_5574.lax_universes);
        type_of = (uu___123_5574.type_of);
        universe_of = (uu___123_5574.universe_of);
        use_bv_sorts = (uu___123_5574.use_bv_sorts);
        qname_and_index = (uu___123_5574.qname_and_index)
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
      let uu___124_5602 = env in
      {
        solver = (uu___124_5602.solver);
        range = (uu___124_5602.range);
        curmodule = (uu___124_5602.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5602.gamma_cache);
        modules = (uu___124_5602.modules);
        expected_typ = (uu___124_5602.expected_typ);
        sigtab = (uu___124_5602.sigtab);
        is_pattern = (uu___124_5602.is_pattern);
        instantiate_imp = (uu___124_5602.instantiate_imp);
        effects = (uu___124_5602.effects);
        generalize = (uu___124_5602.generalize);
        letrecs = (uu___124_5602.letrecs);
        top_level = (uu___124_5602.top_level);
        check_uvars = (uu___124_5602.check_uvars);
        use_eq = (uu___124_5602.use_eq);
        is_iface = (uu___124_5602.is_iface);
        admit = (uu___124_5602.admit);
        lax = (uu___124_5602.lax);
        lax_universes = (uu___124_5602.lax_universes);
        type_of = (uu___124_5602.type_of);
        universe_of = (uu___124_5602.universe_of);
        use_bv_sorts = (uu___124_5602.use_bv_sorts);
        qname_and_index = (uu___124_5602.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5623 = env in
             {
               solver = (uu___125_5623.solver);
               range = (uu___125_5623.range);
               curmodule = (uu___125_5623.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5623.gamma_cache);
               modules = (uu___125_5623.modules);
               expected_typ = (uu___125_5623.expected_typ);
               sigtab = (uu___125_5623.sigtab);
               is_pattern = (uu___125_5623.is_pattern);
               instantiate_imp = (uu___125_5623.instantiate_imp);
               effects = (uu___125_5623.effects);
               generalize = (uu___125_5623.generalize);
               letrecs = (uu___125_5623.letrecs);
               top_level = (uu___125_5623.top_level);
               check_uvars = (uu___125_5623.check_uvars);
               use_eq = (uu___125_5623.use_eq);
               is_iface = (uu___125_5623.is_iface);
               admit = (uu___125_5623.admit);
               lax = (uu___125_5623.lax);
               lax_universes = (uu___125_5623.lax_universes);
               type_of = (uu___125_5623.type_of);
               universe_of = (uu___125_5623.universe_of);
               use_bv_sorts = (uu___125_5623.use_bv_sorts);
               qname_and_index = (uu___125_5623.qname_and_index)
             }))
    | uu____5624 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5637  ->
             match uu____5637 with | (x,uu____5641) -> push_bv env1 x) env bs
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
            let uu___126_5661 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5661.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5661.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (snd t)
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
      (let uu___127_5691 = env in
       {
         solver = (uu___127_5691.solver);
         range = (uu___127_5691.range);
         curmodule = (uu___127_5691.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5691.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5691.sigtab);
         is_pattern = (uu___127_5691.is_pattern);
         instantiate_imp = (uu___127_5691.instantiate_imp);
         effects = (uu___127_5691.effects);
         generalize = (uu___127_5691.generalize);
         letrecs = (uu___127_5691.letrecs);
         top_level = (uu___127_5691.top_level);
         check_uvars = (uu___127_5691.check_uvars);
         use_eq = (uu___127_5691.use_eq);
         is_iface = (uu___127_5691.is_iface);
         admit = (uu___127_5691.admit);
         lax = (uu___127_5691.lax);
         lax_universes = (uu___127_5691.lax_universes);
         type_of = (uu___127_5691.type_of);
         universe_of = (uu___127_5691.universe_of);
         use_bv_sorts = (uu___127_5691.use_bv_sorts);
         qname_and_index = (uu___127_5691.qname_and_index)
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
        let uu____5715 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5715 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5731 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5731)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5741 = env in
      {
        solver = (uu___128_5741.solver);
        range = (uu___128_5741.range);
        curmodule = (uu___128_5741.curmodule);
        gamma = (uu___128_5741.gamma);
        gamma_cache = (uu___128_5741.gamma_cache);
        modules = (uu___128_5741.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5741.sigtab);
        is_pattern = (uu___128_5741.is_pattern);
        instantiate_imp = (uu___128_5741.instantiate_imp);
        effects = (uu___128_5741.effects);
        generalize = (uu___128_5741.generalize);
        letrecs = (uu___128_5741.letrecs);
        top_level = (uu___128_5741.top_level);
        check_uvars = (uu___128_5741.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5741.is_iface);
        admit = (uu___128_5741.admit);
        lax = (uu___128_5741.lax);
        lax_universes = (uu___128_5741.lax_universes);
        type_of = (uu___128_5741.type_of);
        universe_of = (uu___128_5741.universe_of);
        use_bv_sorts = (uu___128_5741.use_bv_sorts);
        qname_and_index = (uu___128_5741.qname_and_index)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5757 = expected_typ env_ in
    ((let uu___129_5760 = env_ in
      {
        solver = (uu___129_5760.solver);
        range = (uu___129_5760.range);
        curmodule = (uu___129_5760.curmodule);
        gamma = (uu___129_5760.gamma);
        gamma_cache = (uu___129_5760.gamma_cache);
        modules = (uu___129_5760.modules);
        expected_typ = None;
        sigtab = (uu___129_5760.sigtab);
        is_pattern = (uu___129_5760.is_pattern);
        instantiate_imp = (uu___129_5760.instantiate_imp);
        effects = (uu___129_5760.effects);
        generalize = (uu___129_5760.generalize);
        letrecs = (uu___129_5760.letrecs);
        top_level = (uu___129_5760.top_level);
        check_uvars = (uu___129_5760.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5760.is_iface);
        admit = (uu___129_5760.admit);
        lax = (uu___129_5760.lax);
        lax_universes = (uu___129_5760.lax_universes);
        type_of = (uu___129_5760.type_of);
        universe_of = (uu___129_5760.universe_of);
        use_bv_sorts = (uu___129_5760.use_bv_sorts);
        qname_and_index = (uu___129_5760.qname_and_index)
      }), uu____5757)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5771 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5775  ->
                    match uu___108_5775 with
                    | Binding_sig (uu____5777,se) -> [se]
                    | uu____5781 -> [])) in
          FStar_All.pipe_right uu____5771 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5786 = env in
       {
         solver = (uu___130_5786.solver);
         range = (uu___130_5786.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5786.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5786.expected_typ);
         sigtab = (uu___130_5786.sigtab);
         is_pattern = (uu___130_5786.is_pattern);
         instantiate_imp = (uu___130_5786.instantiate_imp);
         effects = (uu___130_5786.effects);
         generalize = (uu___130_5786.generalize);
         letrecs = (uu___130_5786.letrecs);
         top_level = (uu___130_5786.top_level);
         check_uvars = (uu___130_5786.check_uvars);
         use_eq = (uu___130_5786.use_eq);
         is_iface = (uu___130_5786.is_iface);
         admit = (uu___130_5786.admit);
         lax = (uu___130_5786.lax);
         lax_universes = (uu___130_5786.lax_universes);
         type_of = (uu___130_5786.type_of);
         universe_of = (uu___130_5786.universe_of);
         use_bv_sorts = (uu___130_5786.use_bv_sorts);
         qname_and_index = (uu___130_5786.qname_and_index)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5836)::tl1 -> aux out tl1
      | (Binding_lid (uu____5839,(uu____5840,t)))::tl1 ->
          let uu____5849 =
            let uu____5853 = FStar_Syntax_Free.uvars t in ext out uu____5853 in
          aux uu____5849 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5857;
            FStar_Syntax_Syntax.index = uu____5858;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5864 =
            let uu____5868 = FStar_Syntax_Free.uvars t in ext out uu____5868 in
          aux uu____5864 tl1
      | (Binding_sig uu____5872)::uu____5873 -> out
      | (Binding_sig_inst uu____5878)::uu____5879 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5916)::tl1 -> aux out tl1
      | (Binding_univ uu____5923)::tl1 -> aux out tl1
      | (Binding_lid (uu____5926,(uu____5927,t)))::tl1 ->
          let uu____5936 =
            let uu____5938 = FStar_Syntax_Free.univs t in ext out uu____5938 in
          aux uu____5936 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5940;
            FStar_Syntax_Syntax.index = uu____5941;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5947 =
            let uu____5949 = FStar_Syntax_Free.univs t in ext out uu____5949 in
          aux uu____5947 tl1
      | (Binding_sig uu____5951)::uu____5952 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5989)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5999 = FStar_Util.set_add uname out in aux uu____5999 tl1
      | (Binding_lid (uu____6001,(uu____6002,t)))::tl1 ->
          let uu____6011 =
            let uu____6013 = FStar_Syntax_Free.univnames t in
            ext out uu____6013 in
          aux uu____6011 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6015;
            FStar_Syntax_Syntax.index = uu____6016;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6022 =
            let uu____6024 = FStar_Syntax_Free.univnames t in
            ext out uu____6024 in
          aux uu____6022 tl1
      | (Binding_sig uu____6026)::uu____6027 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6043  ->
            match uu___109_6043 with
            | Binding_var x -> [x]
            | Binding_lid uu____6046 -> []
            | Binding_sig uu____6049 -> []
            | Binding_univ uu____6053 -> []
            | Binding_sig_inst uu____6054 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6064 =
      let uu____6066 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6066
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6064 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6082 =
      let uu____6083 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6087  ->
                match uu___110_6087 with
                | Binding_var x ->
                    let uu____6089 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6089
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6092) ->
                    let uu____6093 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6093
                | Binding_sig (ls,uu____6095) ->
                    let uu____6098 =
                      let uu____6099 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6099
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6098
                | Binding_sig_inst (ls,uu____6105,uu____6106) ->
                    let uu____6109 =
                      let uu____6110 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6110
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6109)) in
      FStar_All.pipe_right uu____6083 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6082 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6122 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6122
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6139  ->
                 fun uu____6140  ->
                   match (uu____6139, uu____6140) with
                   | ((b1,uu____6150),(b2,uu____6152)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6195  ->
             match uu___111_6195 with
             | Binding_sig (lids,uu____6199) -> FStar_List.append lids keys
             | uu____6202 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6204  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6208  -> ());
    push = (fun uu____6209  -> ());
    pop = (fun uu____6210  -> ());
    mark = (fun uu____6211  -> ());
    reset_mark = (fun uu____6212  -> ());
    commit_mark = (fun uu____6213  -> ());
    encode_modul = (fun uu____6214  -> fun uu____6215  -> ());
    encode_sig = (fun uu____6216  -> fun uu____6217  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6224  -> fun uu____6225  -> fun uu____6226  -> ());
    is_trivial = (fun uu____6230  -> fun uu____6231  -> false);
    finish = (fun uu____6232  -> ());
    refresh = (fun uu____6233  -> ())
  }