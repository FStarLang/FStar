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
               (fun uu____1352  ->
                  match uu____1352 with
                  | (m,uu____1356) -> FStar_Ident.lid_equals l m)) in
        (match uu____1337 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1361 = env in
               {
                 solver = (uu___113_1361.solver);
                 range = (uu___113_1361.range);
                 curmodule = (uu___113_1361.curmodule);
                 gamma = (uu___113_1361.gamma);
                 gamma_cache = (uu___113_1361.gamma_cache);
                 modules = (uu___113_1361.modules);
                 expected_typ = (uu___113_1361.expected_typ);
                 sigtab = (uu___113_1361.sigtab);
                 is_pattern = (uu___113_1361.is_pattern);
                 instantiate_imp = (uu___113_1361.instantiate_imp);
                 effects = (uu___113_1361.effects);
                 generalize = (uu___113_1361.generalize);
                 letrecs = (uu___113_1361.letrecs);
                 top_level = (uu___113_1361.top_level);
                 check_uvars = (uu___113_1361.check_uvars);
                 use_eq = (uu___113_1361.use_eq);
                 is_iface = (uu___113_1361.is_iface);
                 admit = (uu___113_1361.admit);
                 lax = (uu___113_1361.lax);
                 lax_universes = (uu___113_1361.lax_universes);
                 type_of = (uu___113_1361.type_of);
                 universe_of = (uu___113_1361.universe_of);
                 use_bv_sorts = (uu___113_1361.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1364,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1370 = env in
               {
                 solver = (uu___114_1370.solver);
                 range = (uu___114_1370.range);
                 curmodule = (uu___114_1370.curmodule);
                 gamma = (uu___114_1370.gamma);
                 gamma_cache = (uu___114_1370.gamma_cache);
                 modules = (uu___114_1370.modules);
                 expected_typ = (uu___114_1370.expected_typ);
                 sigtab = (uu___114_1370.sigtab);
                 is_pattern = (uu___114_1370.is_pattern);
                 instantiate_imp = (uu___114_1370.instantiate_imp);
                 effects = (uu___114_1370.effects);
                 generalize = (uu___114_1370.generalize);
                 letrecs = (uu___114_1370.letrecs);
                 top_level = (uu___114_1370.top_level);
                 check_uvars = (uu___114_1370.check_uvars);
                 use_eq = (uu___114_1370.use_eq);
                 is_iface = (uu___114_1370.is_iface);
                 admit = (uu___114_1370.admit);
                 lax = (uu___114_1370.lax);
                 lax_universes = (uu___114_1370.lax_universes);
                 type_of = (uu___114_1370.type_of);
                 universe_of = (uu___114_1370.universe_of);
                 use_bv_sorts = (uu___114_1370.use_bv_sorts);
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
        (let uu___115_1386 = e in
         {
           solver = (uu___115_1386.solver);
           range = r;
           curmodule = (uu___115_1386.curmodule);
           gamma = (uu___115_1386.gamma);
           gamma_cache = (uu___115_1386.gamma_cache);
           modules = (uu___115_1386.modules);
           expected_typ = (uu___115_1386.expected_typ);
           sigtab = (uu___115_1386.sigtab);
           is_pattern = (uu___115_1386.is_pattern);
           instantiate_imp = (uu___115_1386.instantiate_imp);
           effects = (uu___115_1386.effects);
           generalize = (uu___115_1386.generalize);
           letrecs = (uu___115_1386.letrecs);
           top_level = (uu___115_1386.top_level);
           check_uvars = (uu___115_1386.check_uvars);
           use_eq = (uu___115_1386.use_eq);
           is_iface = (uu___115_1386.is_iface);
           admit = (uu___115_1386.admit);
           lax = (uu___115_1386.lax);
           lax_universes = (uu___115_1386.lax_universes);
           type_of = (uu___115_1386.type_of);
           universe_of = (uu___115_1386.universe_of);
           use_bv_sorts = (uu___115_1386.use_bv_sorts);
           qname_and_index = (uu___115_1386.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1403 = env in
      {
        solver = (uu___116_1403.solver);
        range = (uu___116_1403.range);
        curmodule = lid;
        gamma = (uu___116_1403.gamma);
        gamma_cache = (uu___116_1403.gamma_cache);
        modules = (uu___116_1403.modules);
        expected_typ = (uu___116_1403.expected_typ);
        sigtab = (uu___116_1403.sigtab);
        is_pattern = (uu___116_1403.is_pattern);
        instantiate_imp = (uu___116_1403.instantiate_imp);
        effects = (uu___116_1403.effects);
        generalize = (uu___116_1403.generalize);
        letrecs = (uu___116_1403.letrecs);
        top_level = (uu___116_1403.top_level);
        check_uvars = (uu___116_1403.check_uvars);
        use_eq = (uu___116_1403.use_eq);
        is_iface = (uu___116_1403.is_iface);
        admit = (uu___116_1403.admit);
        lax = (uu___116_1403.lax);
        lax_universes = (uu___116_1403.lax_universes);
        type_of = (uu___116_1403.type_of);
        universe_of = (uu___116_1403.universe_of);
        use_bv_sorts = (uu___116_1403.use_bv_sorts);
        qname_and_index = (uu___116_1403.qname_and_index)
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
    let uu____1426 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1426
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1429  ->
    let uu____1430 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1430
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1454) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1473 = FStar_Syntax_Subst.subst vs t in (us, uu____1473)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1478  ->
    match uu___100_1478 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1493  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1503 = inst_tscheme t in
      match uu____1503 with
      | (us,t1) ->
          let uu____1510 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1510)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1522  ->
          match uu____1522 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1536 =
                         let uu____1537 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1540 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1543 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1544 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1537 uu____1540 uu____1543 uu____1544 in
                       failwith uu____1536)
                    else ();
                    (let uu____1546 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1546))
               | uu____1550 ->
                   let uu____1551 =
                     let uu____1552 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1552 in
                   failwith uu____1551)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1556 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1560 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1564 -> false
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
             | ([],uu____1590) -> Maybe
             | (uu____1594,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1606 -> No in
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
          let uu____1666 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1666 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1691  ->
                   match uu___101_1691 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1714 =
                           let uu____1724 =
                             let uu____1732 = inst_tscheme t in
                             FStar_Util.Inl uu____1732 in
                           (uu____1724, (FStar_Ident.range_of_lid l)) in
                         Some uu____1714
                       else None
                   | Binding_sig
                       (uu____1766,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1768);
                                     FStar_Syntax_Syntax.sigrng = uu____1769;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1770;
                                     FStar_Syntax_Syntax.sigmeta = uu____1771;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1782 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1782
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1809 ->
                             Some t
                         | uu____1813 -> cache t in
                       let uu____1814 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1814 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1854 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1854 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1898 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1940 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1940
         then
           let uu____1951 = find_in_sigtab env lid in
           match uu____1951 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2017) ->
          add_sigelts env ses
      | uu____2022 ->
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
            | uu____2034 -> ()))
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
        (fun uu___102_2054  ->
           match uu___102_2054 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2067 -> None)
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
          ((uu____2088,lb::[]),uu____2090,uu____2091) ->
          let uu____2100 =
            let uu____2105 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2111 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2105, uu____2111) in
          Some uu____2100
      | FStar_Syntax_Syntax.Sig_let ((uu____2118,lbs),uu____2120,uu____2121)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2143 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2150 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2150
                   then
                     let uu____2156 =
                       let uu____2161 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2167 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2161, uu____2167) in
                     Some uu____2156
                   else None)
      | uu____2179 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2198 =
          let uu____2203 =
            let uu____2206 =
              let uu____2207 =
                let uu____2210 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2210 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2207) in
            inst_tscheme uu____2206 in
          (uu____2203, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2198
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2224,uu____2225) ->
        let uu____2228 =
          let uu____2233 =
            let uu____2236 =
              let uu____2237 =
                let uu____2240 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2240 in
              (us, uu____2237) in
            inst_tscheme uu____2236 in
          (uu____2233, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2228
    | uu____2251 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2286 =
        match uu____2286 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2336,uvs,t,uu____2339,uu____2340,uu____2341);
                    FStar_Syntax_Syntax.sigrng = uu____2342;
                    FStar_Syntax_Syntax.sigquals = uu____2343;
                    FStar_Syntax_Syntax.sigmeta = uu____2344;_},None
                  )
                 ->
                 let uu____2354 =
                   let uu____2359 = inst_tscheme (uvs, t) in
                   (uu____2359, rng) in
                 Some uu____2354
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2371;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2373;_},None
                  )
                 ->
                 let uu____2381 =
                   let uu____2382 = in_cur_mod env l in uu____2382 = Yes in
                 if uu____2381
                 then
                   let uu____2388 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2388
                    then
                      let uu____2395 =
                        let uu____2400 = inst_tscheme (uvs, t) in
                        (uu____2400, rng) in
                      Some uu____2395
                    else None)
                 else
                   (let uu____2415 =
                      let uu____2420 = inst_tscheme (uvs, t) in
                      (uu____2420, rng) in
                    Some uu____2415)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2433,uu____2434);
                    FStar_Syntax_Syntax.sigrng = uu____2435;
                    FStar_Syntax_Syntax.sigquals = uu____2436;
                    FStar_Syntax_Syntax.sigmeta = uu____2437;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2456 =
                        let uu____2461 = inst_tscheme (uvs, k) in
                        (uu____2461, rng) in
                      Some uu____2456
                  | uu____2470 ->
                      let uu____2471 =
                        let uu____2476 =
                          let uu____2479 =
                            let uu____2480 =
                              let uu____2483 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2483 in
                            (uvs, uu____2480) in
                          inst_tscheme uu____2479 in
                        (uu____2476, rng) in
                      Some uu____2471)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2498,uu____2499);
                    FStar_Syntax_Syntax.sigrng = uu____2500;
                    FStar_Syntax_Syntax.sigquals = uu____2501;
                    FStar_Syntax_Syntax.sigmeta = uu____2502;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2522 =
                        let uu____2527 = inst_tscheme_with (uvs, k) us in
                        (uu____2527, rng) in
                      Some uu____2522
                  | uu____2536 ->
                      let uu____2537 =
                        let uu____2542 =
                          let uu____2545 =
                            let uu____2546 =
                              let uu____2549 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2549 in
                            (uvs, uu____2546) in
                          inst_tscheme_with uu____2545 us in
                        (uu____2542, rng) in
                      Some uu____2537)
             | FStar_Util.Inr se ->
                 let uu____2569 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2580;
                        FStar_Syntax_Syntax.sigrng = uu____2581;
                        FStar_Syntax_Syntax.sigquals = uu____2582;
                        FStar_Syntax_Syntax.sigmeta = uu____2583;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2592 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2569
                   (FStar_Util.map_option
                      (fun uu____2618  ->
                         match uu____2618 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2635 =
        let uu____2641 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2641 mapper in
      match uu____2635 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2694 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2694.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2694.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2694.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2715 = lookup_qname env l in
      match uu____2715 with | None  -> false | Some uu____2735 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2763 = try_lookup_bv env bv in
      match uu____2763 with
      | None  ->
          let uu____2771 =
            let uu____2772 =
              let uu____2775 = variable_not_found bv in (uu____2775, bvr) in
            FStar_Errors.Error uu____2772 in
          raise uu____2771
      | Some (t,r) ->
          let uu____2782 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2783 = FStar_Range.set_use_range r bvr in
          (uu____2782, uu____2783)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2795 = try_lookup_lid_aux env l in
      match uu____2795 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2837 =
            let uu____2842 =
              let uu____2845 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2845) in
            (uu____2842, r1) in
          Some uu____2837
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2862 = try_lookup_lid env l in
      match uu____2862 with
      | None  ->
          let uu____2876 =
            let uu____2877 =
              let uu____2880 = name_not_found l in
              (uu____2880, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2877 in
          raise uu____2876
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2903  ->
              match uu___103_2903 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2905 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2916 = lookup_qname env lid in
      match uu____2916 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2931,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2934;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2936;_},None
            ),uu____2937)
          ->
          let uu____2961 =
            let uu____2967 =
              let uu____2970 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2970) in
            (uu____2967, q) in
          Some uu____2961
      | uu____2979 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3001 = lookup_qname env lid in
      match uu____3001 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3014,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3017;
              FStar_Syntax_Syntax.sigquals = uu____3018;
              FStar_Syntax_Syntax.sigmeta = uu____3019;_},None
            ),uu____3020)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3044 ->
          let uu____3055 =
            let uu____3056 =
              let uu____3059 = name_not_found lid in
              (uu____3059, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3056 in
          raise uu____3055
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3070 = lookup_qname env lid in
      match uu____3070 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3083,uvs,t,uu____3086,uu____3087,uu____3088);
              FStar_Syntax_Syntax.sigrng = uu____3089;
              FStar_Syntax_Syntax.sigquals = uu____3090;
              FStar_Syntax_Syntax.sigmeta = uu____3091;_},None
            ),uu____3092)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3118 ->
          let uu____3129 =
            let uu____3130 =
              let uu____3133 = name_not_found lid in
              (uu____3133, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3130 in
          raise uu____3129
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3145 = lookup_qname env lid in
      match uu____3145 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3159,uu____3160,uu____3161,uu____3162,uu____3163,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3165;
              FStar_Syntax_Syntax.sigquals = uu____3166;
              FStar_Syntax_Syntax.sigmeta = uu____3167;_},uu____3168),uu____3169)
          -> (true, dcs)
      | uu____3199 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3217 = lookup_qname env lid in
      match uu____3217 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3228,uu____3229,uu____3230,l,uu____3232,uu____3233);
              FStar_Syntax_Syntax.sigrng = uu____3234;
              FStar_Syntax_Syntax.sigquals = uu____3235;
              FStar_Syntax_Syntax.sigmeta = uu____3236;_},uu____3237),uu____3238)
          -> l
      | uu____3265 ->
          let uu____3276 =
            let uu____3277 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3277 in
          failwith uu____3276
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
        let uu____3302 = lookup_qname env lid in
        match uu____3302 with
        | Some (FStar_Util.Inr (se,None ),uu____3317) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3343,lbs),uu____3345,uu____3346) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3366 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3366
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3387 -> None)
        | uu____3390 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3411 = lookup_qname env ftv in
      match uu____3411 with
      | Some (FStar_Util.Inr (se,None ),uu____3424) ->
          let uu____3447 = effect_signature se in
          (match uu____3447 with
           | None  -> None
           | Some ((uu____3458,t),r) ->
               let uu____3467 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3467)
      | uu____3468 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3485 = try_lookup_effect_lid env ftv in
      match uu____3485 with
      | None  ->
          let uu____3487 =
            let uu____3488 =
              let uu____3491 = name_not_found ftv in
              (uu____3491, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3488 in
          raise uu____3487
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
        let uu____3505 = lookup_qname env lid0 in
        match uu____3505 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3523);
                FStar_Syntax_Syntax.sigrng = uu____3524;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3526;_},None
              ),uu____3527)
            ->
            let lid1 =
              let uu____3554 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3554 in
            let uu____3555 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3558  ->
                      match uu___104_3558 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3559 -> false)) in
            if uu____3555
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3572 =
                      let uu____3573 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3574 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3573 uu____3574 in
                    failwith uu____3572) in
               match (binders, univs1) with
               | ([],uu____3580) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3589,uu____3590::uu____3591::uu____3592) ->
                   let uu____3595 =
                     let uu____3596 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3597 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3596 uu____3597 in
                   failwith uu____3595
               | uu____3603 ->
                   let uu____3606 =
                     let uu____3609 =
                       let uu____3610 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3610) in
                     inst_tscheme_with uu____3609 insts in
                   (match uu____3606 with
                    | (uu____3618,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3621 =
                          let uu____3622 = FStar_Syntax_Subst.compress t1 in
                          uu____3622.FStar_Syntax_Syntax.n in
                        (match uu____3621 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3652 -> failwith "Impossible")))
        | uu____3656 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3682 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3682 with
        | None  -> None
        | Some (uu____3689,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3694 = find1 l2 in
            (match uu____3694 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3699 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3699 with
        | Some l1 -> l1
        | None  ->
            let uu____3702 = find1 l in
            (match uu____3702 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3714 = lookup_qname env l1 in
      match uu____3714 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3726;
              FStar_Syntax_Syntax.sigrng = uu____3727;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3729;_},uu____3730),uu____3731)
          -> q
      | uu____3756 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3779 =
          let uu____3780 =
            let uu____3781 = FStar_Util.string_of_int i in
            let uu____3782 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3781 uu____3782 in
          failwith uu____3780 in
        let uu____3783 = lookup_datacon env lid in
        match uu____3783 with
        | (uu____3786,t) ->
            let uu____3788 =
              let uu____3789 = FStar_Syntax_Subst.compress t in
              uu____3789.FStar_Syntax_Syntax.n in
            (match uu____3788 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3793) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3814 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3814 FStar_Pervasives.fst)
             | uu____3819 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3826 = lookup_qname env l in
      match uu____3826 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3837,uu____3838,uu____3839);
              FStar_Syntax_Syntax.sigrng = uu____3840;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3842;_},uu____3843),uu____3844)
          ->
          FStar_Util.for_some
            (fun uu___105_3871  ->
               match uu___105_3871 with
               | FStar_Syntax_Syntax.Projector uu____3872 -> true
               | uu____3875 -> false) quals
      | uu____3876 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3893 = lookup_qname env lid in
      match uu____3893 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3904,uu____3905,uu____3906,uu____3907,uu____3908,uu____3909);
              FStar_Syntax_Syntax.sigrng = uu____3910;
              FStar_Syntax_Syntax.sigquals = uu____3911;
              FStar_Syntax_Syntax.sigmeta = uu____3912;_},uu____3913),uu____3914)
          -> true
      | uu____3941 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3958 = lookup_qname env lid in
      match uu____3958 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3969,uu____3970,uu____3971,uu____3972,uu____3973,uu____3974);
              FStar_Syntax_Syntax.sigrng = uu____3975;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3977;_},uu____3978),uu____3979)
          ->
          FStar_Util.for_some
            (fun uu___106_4010  ->
               match uu___106_4010 with
               | FStar_Syntax_Syntax.RecordType uu____4011 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4016 -> true
               | uu____4021 -> false) quals
      | uu____4022 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4039 = lookup_qname env lid in
      match uu____4039 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4050,uu____4051,uu____4052);
              FStar_Syntax_Syntax.sigrng = uu____4053;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4055;_},uu____4056),uu____4057)
          ->
          FStar_Util.for_some
            (fun uu___107_4088  ->
               match uu___107_4088 with
               | FStar_Syntax_Syntax.Action uu____4089 -> true
               | uu____4090 -> false) quals
      | uu____4091 -> false
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
      let uu____4110 =
        let uu____4111 = FStar_Syntax_Util.un_uinst head1 in
        uu____4111.FStar_Syntax_Syntax.n in
      match uu____4110 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4115 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4153 -> Some false
        | FStar_Util.Inr (se,uu____4162) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4171 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4175 -> Some true
             | uu____4184 -> Some false) in
      let uu____4185 =
        let uu____4187 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4187 mapper in
      match uu____4185 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4214 = lookup_qname env lid in
      match uu____4214 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4225,uu____4226,tps,uu____4228,uu____4229,uu____4230);
              FStar_Syntax_Syntax.sigrng = uu____4231;
              FStar_Syntax_Syntax.sigquals = uu____4232;
              FStar_Syntax_Syntax.sigmeta = uu____4233;_},uu____4234),uu____4235)
          -> FStar_List.length tps
      | uu____4267 ->
          let uu____4278 =
            let uu____4279 =
              let uu____4282 = name_not_found lid in
              (uu____4282, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4279 in
          raise uu____4278
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
           (fun uu____4307  ->
              match uu____4307 with
              | (d,uu____4312) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4321 = effect_decl_opt env l in
      match uu____4321 with
      | None  ->
          let uu____4329 =
            let uu____4330 =
              let uu____4333 = name_not_found l in
              (uu____4333, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4330 in
          raise uu____4329
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
            (let uu____4380 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4410  ->
                       match uu____4410 with
                       | (m1,m2,uu____4418,uu____4419,uu____4420) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4380 with
             | None  ->
                 let uu____4429 =
                   let uu____4430 =
                     let uu____4433 =
                       let uu____4434 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4435 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4434
                         uu____4435 in
                     (uu____4433, (env.range)) in
                   FStar_Errors.Error uu____4430 in
                 raise uu____4429
             | Some (uu____4439,uu____4440,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4487 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4502  ->
            match uu____4502 with
            | (d,uu____4506) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4487 with
  | None  ->
      let uu____4513 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4513
  | Some (md,_q) ->
      let uu____4522 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4522 with
       | (uu____4529,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4537)::(wp,uu____4539)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4561 -> failwith "Impossible"))
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
                 let uu____4597 = get_range env in
                 let uu____4598 =
                   let uu____4601 =
                     let uu____4602 =
                       let uu____4612 =
                         let uu____4614 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4614] in
                       (null_wp, uu____4612) in
                     FStar_Syntax_Syntax.Tm_app uu____4602 in
                   FStar_Syntax_Syntax.mk uu____4601 in
                 uu____4598 None uu____4597 in
               let uu____4624 =
                 let uu____4625 =
                   let uu____4631 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4631] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4625;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4624)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4640 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4640.order);
              joins = (uu___118_4640.joins)
            } in
          let uu___119_4645 = env in
          {
            solver = (uu___119_4645.solver);
            range = (uu___119_4645.range);
            curmodule = (uu___119_4645.curmodule);
            gamma = (uu___119_4645.gamma);
            gamma_cache = (uu___119_4645.gamma_cache);
            modules = (uu___119_4645.modules);
            expected_typ = (uu___119_4645.expected_typ);
            sigtab = (uu___119_4645.sigtab);
            is_pattern = (uu___119_4645.is_pattern);
            instantiate_imp = (uu___119_4645.instantiate_imp);
            effects;
            generalize = (uu___119_4645.generalize);
            letrecs = (uu___119_4645.letrecs);
            top_level = (uu___119_4645.top_level);
            check_uvars = (uu___119_4645.check_uvars);
            use_eq = (uu___119_4645.use_eq);
            is_iface = (uu___119_4645.is_iface);
            admit = (uu___119_4645.admit);
            lax = (uu___119_4645.lax);
            lax_universes = (uu___119_4645.lax_universes);
            type_of = (uu___119_4645.type_of);
            universe_of = (uu___119_4645.universe_of);
            use_bv_sorts = (uu___119_4645.use_bv_sorts);
            qname_and_index = (uu___119_4645.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4662 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4662 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4746 = (e1.mlift).mlift_wp t wp in
                              let uu____4747 = l1 t wp e in
                              l2 t uu____4746 uu____4747))
                | uu____4748 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4783 = inst_tscheme lift_t in
            match uu____4783 with
            | (uu____4788,lift_t1) ->
                let uu____4790 =
                  let uu____4793 =
                    let uu____4794 =
                      let uu____4804 =
                        let uu____4806 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4807 =
                          let uu____4809 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4809] in
                        uu____4806 :: uu____4807 in
                      (lift_t1, uu____4804) in
                    FStar_Syntax_Syntax.Tm_app uu____4794 in
                  FStar_Syntax_Syntax.mk uu____4793 in
                uu____4790 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4854 = inst_tscheme lift_t in
            match uu____4854 with
            | (uu____4859,lift_t1) ->
                let uu____4861 =
                  let uu____4864 =
                    let uu____4865 =
                      let uu____4875 =
                        let uu____4877 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4878 =
                          let uu____4880 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4881 =
                            let uu____4883 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4883] in
                          uu____4880 :: uu____4881 in
                        uu____4877 :: uu____4878 in
                      (lift_t1, uu____4875) in
                    FStar_Syntax_Syntax.Tm_app uu____4865 in
                  FStar_Syntax_Syntax.mk uu____4864 in
                uu____4861 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4924 =
                let uu____4925 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4925
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4924 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4929 =
              let uu____4930 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4930 in
            let uu____4931 =
              let uu____4932 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4949 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4949) in
              FStar_Util.dflt "none" uu____4932 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4929
              uu____4931 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4965  ->
                    match uu____4965 with
                    | (e,uu____4970) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4983 =
            match uu____4983 with
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
              let uu____5009 =
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
                                    (let uu____5023 =
                                       let uu____5028 =
                                         find_edge order1 (i, k) in
                                       let uu____5030 =
                                         find_edge order1 (k, j) in
                                       (uu____5028, uu____5030) in
                                     match uu____5023 with
                                     | (Some e1,Some e2) ->
                                         let uu____5039 = compose_edges e1 e2 in
                                         [uu____5039]
                                     | uu____5040 -> []))))) in
              FStar_List.append order1 uu____5009 in
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
                   let uu____5060 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5062 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5062
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5060
                   then
                     let uu____5065 =
                       let uu____5066 =
                         let uu____5069 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5070 = get_range env in
                         (uu____5069, uu____5070) in
                       FStar_Errors.Error uu____5066 in
                     raise uu____5065
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
                                            let uu____5141 =
                                              let uu____5146 =
                                                find_edge order2 (i, k) in
                                              let uu____5148 =
                                                find_edge order2 (j, k) in
                                              (uu____5146, uu____5148) in
                                            match uu____5141 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5171,uu____5172)
                                                     ->
                                                     let uu____5176 =
                                                       let uu____5179 =
                                                         let uu____5180 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5180 in
                                                       let uu____5182 =
                                                         let uu____5183 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5183 in
                                                       (uu____5179,
                                                         uu____5182) in
                                                     (match uu____5176 with
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
                                            | uu____5202 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5241 = env.effects in
              { decls = (uu___120_5241.decls); order = order2; joins } in
            let uu___121_5242 = env in
            {
              solver = (uu___121_5242.solver);
              range = (uu___121_5242.range);
              curmodule = (uu___121_5242.curmodule);
              gamma = (uu___121_5242.gamma);
              gamma_cache = (uu___121_5242.gamma_cache);
              modules = (uu___121_5242.modules);
              expected_typ = (uu___121_5242.expected_typ);
              sigtab = (uu___121_5242.sigtab);
              is_pattern = (uu___121_5242.is_pattern);
              instantiate_imp = (uu___121_5242.instantiate_imp);
              effects;
              generalize = (uu___121_5242.generalize);
              letrecs = (uu___121_5242.letrecs);
              top_level = (uu___121_5242.top_level);
              check_uvars = (uu___121_5242.check_uvars);
              use_eq = (uu___121_5242.use_eq);
              is_iface = (uu___121_5242.is_iface);
              admit = (uu___121_5242.admit);
              lax = (uu___121_5242.lax);
              lax_universes = (uu___121_5242.lax_universes);
              type_of = (uu___121_5242.type_of);
              universe_of = (uu___121_5242.universe_of);
              use_bv_sorts = (uu___121_5242.use_bv_sorts);
              qname_and_index = (uu___121_5242.qname_and_index)
            }))
      | uu____5243 -> env
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
        | uu____5265 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5273 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5273 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5283 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5283 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5300 =
                     let uu____5301 =
                       let uu____5304 =
                         let uu____5305 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5311 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5319 =
                           let uu____5320 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5320 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5305 uu____5311 uu____5319 in
                       (uu____5304, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5301 in
                   raise uu____5300)
                else ();
                (let inst1 =
                   let uu____5324 =
                     let uu____5330 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5330 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5343  ->
                        fun uu____5344  ->
                          match (uu____5343, uu____5344) with
                          | ((x,uu____5358),(t,uu____5360)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5324 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5375 =
                     let uu___122_5376 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5376.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5376.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5376.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5376.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5375
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5406 =
    let uu____5411 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5411 in
  match uu____5406 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5427 =
        only_reifiable &&
          (let uu____5429 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5429) in
      if uu____5427
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5442 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5444 =
               let uu____5453 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5453) in
             (match uu____5444 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5487 =
                    let uu____5490 = get_range env in
                    let uu____5491 =
                      let uu____5494 =
                        let uu____5495 =
                          let uu____5505 =
                            let uu____5507 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5507; wp] in
                          (repr, uu____5505) in
                        FStar_Syntax_Syntax.Tm_app uu____5495 in
                      FStar_Syntax_Syntax.mk uu____5494 in
                    uu____5491 None uu____5490 in
                  Some uu____5487))
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
          let uu____5551 =
            let uu____5552 =
              let uu____5555 =
                let uu____5556 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5556 in
              let uu____5557 = get_range env in (uu____5555, uu____5557) in
            FStar_Errors.Error uu____5552 in
          raise uu____5551 in
        let uu____5558 = effect_repr_aux true env c u_c in
        match uu____5558 with
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
        | FStar_Util.Inr (eff_name,uu____5590) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5603 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5610 =
        let uu____5611 = FStar_Syntax_Subst.compress t in
        uu____5611.FStar_Syntax_Syntax.n in
      match uu____5610 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5614,c) ->
          is_reifiable_comp env c
      | uu____5626 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5644)::uu____5645 -> x :: rest
        | (Binding_sig_inst uu____5650)::uu____5651 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5660 = push1 x rest1 in local :: uu____5660 in
      let uu___123_5662 = env in
      let uu____5663 = push1 s env.gamma in
      {
        solver = (uu___123_5662.solver);
        range = (uu___123_5662.range);
        curmodule = (uu___123_5662.curmodule);
        gamma = uu____5663;
        gamma_cache = (uu___123_5662.gamma_cache);
        modules = (uu___123_5662.modules);
        expected_typ = (uu___123_5662.expected_typ);
        sigtab = (uu___123_5662.sigtab);
        is_pattern = (uu___123_5662.is_pattern);
        instantiate_imp = (uu___123_5662.instantiate_imp);
        effects = (uu___123_5662.effects);
        generalize = (uu___123_5662.generalize);
        letrecs = (uu___123_5662.letrecs);
        top_level = (uu___123_5662.top_level);
        check_uvars = (uu___123_5662.check_uvars);
        use_eq = (uu___123_5662.use_eq);
        is_iface = (uu___123_5662.is_iface);
        admit = (uu___123_5662.admit);
        lax = (uu___123_5662.lax);
        lax_universes = (uu___123_5662.lax_universes);
        type_of = (uu___123_5662.type_of);
        universe_of = (uu___123_5662.universe_of);
        use_bv_sorts = (uu___123_5662.use_bv_sorts);
        qname_and_index = (uu___123_5662.qname_and_index)
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
      let uu___124_5690 = env in
      {
        solver = (uu___124_5690.solver);
        range = (uu___124_5690.range);
        curmodule = (uu___124_5690.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5690.gamma_cache);
        modules = (uu___124_5690.modules);
        expected_typ = (uu___124_5690.expected_typ);
        sigtab = (uu___124_5690.sigtab);
        is_pattern = (uu___124_5690.is_pattern);
        instantiate_imp = (uu___124_5690.instantiate_imp);
        effects = (uu___124_5690.effects);
        generalize = (uu___124_5690.generalize);
        letrecs = (uu___124_5690.letrecs);
        top_level = (uu___124_5690.top_level);
        check_uvars = (uu___124_5690.check_uvars);
        use_eq = (uu___124_5690.use_eq);
        is_iface = (uu___124_5690.is_iface);
        admit = (uu___124_5690.admit);
        lax = (uu___124_5690.lax);
        lax_universes = (uu___124_5690.lax_universes);
        type_of = (uu___124_5690.type_of);
        universe_of = (uu___124_5690.universe_of);
        use_bv_sorts = (uu___124_5690.use_bv_sorts);
        qname_and_index = (uu___124_5690.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5712 = env in
             {
               solver = (uu___125_5712.solver);
               range = (uu___125_5712.range);
               curmodule = (uu___125_5712.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5712.gamma_cache);
               modules = (uu___125_5712.modules);
               expected_typ = (uu___125_5712.expected_typ);
               sigtab = (uu___125_5712.sigtab);
               is_pattern = (uu___125_5712.is_pattern);
               instantiate_imp = (uu___125_5712.instantiate_imp);
               effects = (uu___125_5712.effects);
               generalize = (uu___125_5712.generalize);
               letrecs = (uu___125_5712.letrecs);
               top_level = (uu___125_5712.top_level);
               check_uvars = (uu___125_5712.check_uvars);
               use_eq = (uu___125_5712.use_eq);
               is_iface = (uu___125_5712.is_iface);
               admit = (uu___125_5712.admit);
               lax = (uu___125_5712.lax);
               lax_universes = (uu___125_5712.lax_universes);
               type_of = (uu___125_5712.type_of);
               universe_of = (uu___125_5712.universe_of);
               use_bv_sorts = (uu___125_5712.use_bv_sorts);
               qname_and_index = (uu___125_5712.qname_and_index)
             }))
    | uu____5713 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5730  ->
             match uu____5730 with | (x,uu____5734) -> push_bv env1 x) env bs
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
            let uu___126_5755 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5755.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5755.FStar_Syntax_Syntax.index);
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
      (let uu___127_5781 = env in
       {
         solver = (uu___127_5781.solver);
         range = (uu___127_5781.range);
         curmodule = (uu___127_5781.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5781.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5781.sigtab);
         is_pattern = (uu___127_5781.is_pattern);
         instantiate_imp = (uu___127_5781.instantiate_imp);
         effects = (uu___127_5781.effects);
         generalize = (uu___127_5781.generalize);
         letrecs = (uu___127_5781.letrecs);
         top_level = (uu___127_5781.top_level);
         check_uvars = (uu___127_5781.check_uvars);
         use_eq = (uu___127_5781.use_eq);
         is_iface = (uu___127_5781.is_iface);
         admit = (uu___127_5781.admit);
         lax = (uu___127_5781.lax);
         lax_universes = (uu___127_5781.lax_universes);
         type_of = (uu___127_5781.type_of);
         universe_of = (uu___127_5781.universe_of);
         use_bv_sorts = (uu___127_5781.use_bv_sorts);
         qname_and_index = (uu___127_5781.qname_and_index)
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
        let uu____5807 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5807 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5823 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5823)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5833 = env in
      {
        solver = (uu___128_5833.solver);
        range = (uu___128_5833.range);
        curmodule = (uu___128_5833.curmodule);
        gamma = (uu___128_5833.gamma);
        gamma_cache = (uu___128_5833.gamma_cache);
        modules = (uu___128_5833.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5833.sigtab);
        is_pattern = (uu___128_5833.is_pattern);
        instantiate_imp = (uu___128_5833.instantiate_imp);
        effects = (uu___128_5833.effects);
        generalize = (uu___128_5833.generalize);
        letrecs = (uu___128_5833.letrecs);
        top_level = (uu___128_5833.top_level);
        check_uvars = (uu___128_5833.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5833.is_iface);
        admit = (uu___128_5833.admit);
        lax = (uu___128_5833.lax);
        lax_universes = (uu___128_5833.lax_universes);
        type_of = (uu___128_5833.type_of);
        universe_of = (uu___128_5833.universe_of);
        use_bv_sorts = (uu___128_5833.use_bv_sorts);
        qname_and_index = (uu___128_5833.qname_and_index)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5849 = expected_typ env_ in
    ((let uu___129_5853 = env_ in
      {
        solver = (uu___129_5853.solver);
        range = (uu___129_5853.range);
        curmodule = (uu___129_5853.curmodule);
        gamma = (uu___129_5853.gamma);
        gamma_cache = (uu___129_5853.gamma_cache);
        modules = (uu___129_5853.modules);
        expected_typ = None;
        sigtab = (uu___129_5853.sigtab);
        is_pattern = (uu___129_5853.is_pattern);
        instantiate_imp = (uu___129_5853.instantiate_imp);
        effects = (uu___129_5853.effects);
        generalize = (uu___129_5853.generalize);
        letrecs = (uu___129_5853.letrecs);
        top_level = (uu___129_5853.top_level);
        check_uvars = (uu___129_5853.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5853.is_iface);
        admit = (uu___129_5853.admit);
        lax = (uu___129_5853.lax);
        lax_universes = (uu___129_5853.lax_universes);
        type_of = (uu___129_5853.type_of);
        universe_of = (uu___129_5853.universe_of);
        use_bv_sorts = (uu___129_5853.use_bv_sorts);
        qname_and_index = (uu___129_5853.qname_and_index)
      }), uu____5849)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5864 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5871  ->
                    match uu___108_5871 with
                    | Binding_sig (uu____5873,se) -> [se]
                    | uu____5877 -> [])) in
          FStar_All.pipe_right uu____5864 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5882 = env in
       {
         solver = (uu___130_5882.solver);
         range = (uu___130_5882.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5882.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5882.expected_typ);
         sigtab = (uu___130_5882.sigtab);
         is_pattern = (uu___130_5882.is_pattern);
         instantiate_imp = (uu___130_5882.instantiate_imp);
         effects = (uu___130_5882.effects);
         generalize = (uu___130_5882.generalize);
         letrecs = (uu___130_5882.letrecs);
         top_level = (uu___130_5882.top_level);
         check_uvars = (uu___130_5882.check_uvars);
         use_eq = (uu___130_5882.use_eq);
         is_iface = (uu___130_5882.is_iface);
         admit = (uu___130_5882.admit);
         lax = (uu___130_5882.lax);
         lax_universes = (uu___130_5882.lax_universes);
         type_of = (uu___130_5882.type_of);
         universe_of = (uu___130_5882.universe_of);
         use_bv_sorts = (uu___130_5882.use_bv_sorts);
         qname_and_index = (uu___130_5882.qname_and_index)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5932)::tl1 -> aux out tl1
      | (Binding_lid (uu____5935,(uu____5936,t)))::tl1 ->
          let uu____5945 =
            let uu____5949 = FStar_Syntax_Free.uvars t in ext out uu____5949 in
          aux uu____5945 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5953;
            FStar_Syntax_Syntax.index = uu____5954;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5960 =
            let uu____5964 = FStar_Syntax_Free.uvars t in ext out uu____5964 in
          aux uu____5960 tl1
      | (Binding_sig uu____5968)::uu____5969 -> out
      | (Binding_sig_inst uu____5974)::uu____5975 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6012)::tl1 -> aux out tl1
      | (Binding_univ uu____6019)::tl1 -> aux out tl1
      | (Binding_lid (uu____6022,(uu____6023,t)))::tl1 ->
          let uu____6032 =
            let uu____6034 = FStar_Syntax_Free.univs t in ext out uu____6034 in
          aux uu____6032 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6036;
            FStar_Syntax_Syntax.index = uu____6037;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6043 =
            let uu____6045 = FStar_Syntax_Free.univs t in ext out uu____6045 in
          aux uu____6043 tl1
      | (Binding_sig uu____6047)::uu____6048 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6085)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6095 = FStar_Util.set_add uname out in aux uu____6095 tl1
      | (Binding_lid (uu____6097,(uu____6098,t)))::tl1 ->
          let uu____6107 =
            let uu____6109 = FStar_Syntax_Free.univnames t in
            ext out uu____6109 in
          aux uu____6107 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6111;
            FStar_Syntax_Syntax.index = uu____6112;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6118 =
            let uu____6120 = FStar_Syntax_Free.univnames t in
            ext out uu____6120 in
          aux uu____6118 tl1
      | (Binding_sig uu____6122)::uu____6123 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6141  ->
            match uu___109_6141 with
            | Binding_var x -> [x]
            | Binding_lid uu____6144 -> []
            | Binding_sig uu____6147 -> []
            | Binding_univ uu____6151 -> []
            | Binding_sig_inst uu____6152 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6162 =
      let uu____6164 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6164
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6162 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6180 =
      let uu____6181 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6188  ->
                match uu___110_6188 with
                | Binding_var x ->
                    let uu____6190 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6190
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6193) ->
                    let uu____6194 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6194
                | Binding_sig (ls,uu____6196) ->
                    let uu____6199 =
                      let uu____6200 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6200
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6199
                | Binding_sig_inst (ls,uu____6206,uu____6207) ->
                    let uu____6210 =
                      let uu____6211 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6211
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6210)) in
      FStar_All.pipe_right uu____6181 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6180 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6223 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6223
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6246  ->
                 fun uu____6247  ->
                   match (uu____6246, uu____6247) with
                   | ((b1,uu____6257),(b2,uu____6259)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6308  ->
             match uu___111_6308 with
             | Binding_sig (lids,uu____6312) -> FStar_List.append lids keys
             | uu____6315 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6320  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6326  -> ());
    push = (fun uu____6328  -> ());
    pop = (fun uu____6330  -> ());
    mark = (fun uu____6332  -> ());
    reset_mark = (fun uu____6334  -> ());
    commit_mark = (fun uu____6336  -> ());
    encode_modul = (fun uu____6339  -> fun uu____6340  -> ());
    encode_sig = (fun uu____6343  -> fun uu____6344  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6356  -> fun uu____6357  -> fun uu____6358  -> ());
    is_trivial = (fun uu____6364  -> fun uu____6365  -> false);
    finish = (fun uu____6367  -> ());
    refresh = (fun uu____6369  -> ())
  }