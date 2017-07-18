open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____34 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____48 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____69 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
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
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
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
      FStar_Pervasives_Native.option;}
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list;}
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option;}
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
  preprocess:
    env -> goal -> (env,goal) FStar_Pervasives_Native.tuple2 Prims.list;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list;}
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list
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
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
         FStar_Pervasives_Native.tuple3)
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
            expected_typ = FStar_Pervasives_Native.None;
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
            qname_and_index = FStar_Pervasives_Native.None
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]]
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
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____1136  ->
    match uu____1136 with
    | (l,n1) ->
        let uu____1141 = FStar_ST.read query_indices in
        (match uu____1141 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1175 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
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
    (let uu___111_1266 = env in
     let uu____1267 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1269 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___111_1266.solver);
       range = (uu___111_1266.range);
       curmodule = (uu___111_1266.curmodule);
       gamma = (uu___111_1266.gamma);
       gamma_cache = uu____1267;
       modules = (uu___111_1266.modules);
       expected_typ = (uu___111_1266.expected_typ);
       sigtab = uu____1269;
       is_pattern = (uu___111_1266.is_pattern);
       instantiate_imp = (uu___111_1266.instantiate_imp);
       effects = (uu___111_1266.effects);
       generalize = (uu___111_1266.generalize);
       letrecs = (uu___111_1266.letrecs);
       top_level = (uu___111_1266.top_level);
       check_uvars = (uu___111_1266.check_uvars);
       use_eq = (uu___111_1266.use_eq);
       is_iface = (uu___111_1266.is_iface);
       admit = (uu___111_1266.admit);
       lax = (uu___111_1266.lax);
       lax_universes = (uu___111_1266.lax_universes);
       type_of = (uu___111_1266.type_of);
       universe_of = (uu___111_1266.universe_of);
       use_bv_sorts = (uu___111_1266.use_bv_sorts);
       qname_and_index = (uu___111_1266.qname_and_index)
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
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____1337 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1349  ->
                  match uu____1349 with
                  | (m,uu____1353) -> FStar_Ident.lid_equals l m)) in
        (match uu____1337 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___112_1358 = env in
               {
                 solver = (uu___112_1358.solver);
                 range = (uu___112_1358.range);
                 curmodule = (uu___112_1358.curmodule);
                 gamma = (uu___112_1358.gamma);
                 gamma_cache = (uu___112_1358.gamma_cache);
                 modules = (uu___112_1358.modules);
                 expected_typ = (uu___112_1358.expected_typ);
                 sigtab = (uu___112_1358.sigtab);
                 is_pattern = (uu___112_1358.is_pattern);
                 instantiate_imp = (uu___112_1358.instantiate_imp);
                 effects = (uu___112_1358.effects);
                 generalize = (uu___112_1358.generalize);
                 letrecs = (uu___112_1358.letrecs);
                 top_level = (uu___112_1358.top_level);
                 check_uvars = (uu___112_1358.check_uvars);
                 use_eq = (uu___112_1358.use_eq);
                 is_iface = (uu___112_1358.is_iface);
                 admit = (uu___112_1358.admit);
                 lax = (uu___112_1358.lax);
                 lax_universes = (uu___112_1358.lax_universes);
                 type_of = (uu___112_1358.type_of);
                 universe_of = (uu___112_1358.universe_of);
                 use_bv_sorts = (uu___112_1358.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next))
               }))
         | FStar_Pervasives_Native.Some (uu____1361,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1367 = env in
               {
                 solver = (uu___113_1367.solver);
                 range = (uu___113_1367.range);
                 curmodule = (uu___113_1367.curmodule);
                 gamma = (uu___113_1367.gamma);
                 gamma_cache = (uu___113_1367.gamma_cache);
                 modules = (uu___113_1367.modules);
                 expected_typ = (uu___113_1367.expected_typ);
                 sigtab = (uu___113_1367.sigtab);
                 is_pattern = (uu___113_1367.is_pattern);
                 instantiate_imp = (uu___113_1367.instantiate_imp);
                 effects = (uu___113_1367.effects);
                 generalize = (uu___113_1367.generalize);
                 letrecs = (uu___113_1367.letrecs);
                 top_level = (uu___113_1367.top_level);
                 check_uvars = (uu___113_1367.check_uvars);
                 use_eq = (uu___113_1367.use_eq);
                 is_iface = (uu___113_1367.is_iface);
                 admit = (uu___113_1367.admit);
                 lax = (uu___113_1367.lax);
                 lax_universes = (uu___113_1367.lax_universes);
                 type_of = (uu___113_1367.type_of);
                 universe_of = (uu___113_1367.universe_of);
                 use_bv_sorts = (uu___113_1367.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next))
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
        (let uu___114_1383 = e in
         {
           solver = (uu___114_1383.solver);
           range = r;
           curmodule = (uu___114_1383.curmodule);
           gamma = (uu___114_1383.gamma);
           gamma_cache = (uu___114_1383.gamma_cache);
           modules = (uu___114_1383.modules);
           expected_typ = (uu___114_1383.expected_typ);
           sigtab = (uu___114_1383.sigtab);
           is_pattern = (uu___114_1383.is_pattern);
           instantiate_imp = (uu___114_1383.instantiate_imp);
           effects = (uu___114_1383.effects);
           generalize = (uu___114_1383.generalize);
           letrecs = (uu___114_1383.letrecs);
           top_level = (uu___114_1383.top_level);
           check_uvars = (uu___114_1383.check_uvars);
           use_eq = (uu___114_1383.use_eq);
           is_iface = (uu___114_1383.is_iface);
           admit = (uu___114_1383.admit);
           lax = (uu___114_1383.lax);
           lax_universes = (uu___114_1383.lax_universes);
           type_of = (uu___114_1383.type_of);
           universe_of = (uu___114_1383.universe_of);
           use_bv_sorts = (uu___114_1383.use_bv_sorts);
           qname_and_index = (uu___114_1383.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___115_1400 = env in
      {
        solver = (uu___115_1400.solver);
        range = (uu___115_1400.range);
        curmodule = lid;
        gamma = (uu___115_1400.gamma);
        gamma_cache = (uu___115_1400.gamma_cache);
        modules = (uu___115_1400.modules);
        expected_typ = (uu___115_1400.expected_typ);
        sigtab = (uu___115_1400.sigtab);
        is_pattern = (uu___115_1400.is_pattern);
        instantiate_imp = (uu___115_1400.instantiate_imp);
        effects = (uu___115_1400.effects);
        generalize = (uu___115_1400.generalize);
        letrecs = (uu___115_1400.letrecs);
        top_level = (uu___115_1400.top_level);
        check_uvars = (uu___115_1400.check_uvars);
        use_eq = (uu___115_1400.use_eq);
        is_iface = (uu___115_1400.is_iface);
        admit = (uu___115_1400.admit);
        lax = (uu___115_1400.lax);
        lax_universes = (uu___115_1400.lax_universes);
        type_of = (uu___115_1400.type_of);
        universe_of = (uu___115_1400.universe_of);
        use_bv_sorts = (uu___115_1400.use_bv_sorts);
        qname_and_index = (uu___115_1400.qname_and_index)
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
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
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
    let uu____1426 = FStar_Unionfind.fresh FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.U_unif uu____1426
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1449) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1465 = FStar_Syntax_Subst.subst vs t in (us, uu____1465)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___99_1470  ->
    match uu___99_1470 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1484  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____1494 = inst_tscheme t in
      match uu____1494 with
      | (us,t1) ->
          let uu____1501 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1501)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1513  ->
          match uu____1513 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1527 =
                         let uu____1528 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1531 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1534 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1535 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1528 uu____1531 uu____1534 uu____1535 in
                       failwith uu____1527)
                    else ();
                    (let uu____1537 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____1537))
               | uu____1541 ->
                   let uu____1542 =
                     let uu____1543 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1543 in
                   failwith uu____1542)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1547 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1551 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1555 -> false
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
             | ([],uu____1581) -> Maybe
             | (uu____1585,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1597 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____1657 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1657 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___100_1678  ->
                   match uu___100_1678 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1701 =
                           let uu____1711 =
                             let uu____1719 = inst_tscheme t in
                             FStar_Util.Inl uu____1719 in
                           (uu____1711, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____1701
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____1753,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1755);
                                     FStar_Syntax_Syntax.sigrng = uu____1756;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1757;
                                     FStar_Syntax_Syntax.sigmeta = uu____1758;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1767 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1767
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1794 ->
                             FStar_Pervasives_Native.Some t
                         | uu____1798 -> cache t in
                       let uu____1799 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1799 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1839 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1839 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1883 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1925 = find_in_sigtab env lid in
         match uu____1925 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1981) ->
          add_sigelts env ses
      | uu____1986 ->
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
            | uu____1995 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___101_2013  ->
           match uu___101_2013 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2026 -> FStar_Pervasives_Native.None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2047,lb::[]),uu____2049,uu____2050) ->
          let uu____2059 =
            let uu____2064 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2070 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2064, uu____2070) in
          FStar_Pervasives_Native.Some uu____2059
      | FStar_Syntax_Syntax.Sig_let ((uu____2077,lbs),uu____2079,uu____2080)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2100 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2107 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2107
                   then
                     let uu____2113 =
                       let uu____2118 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2124 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2118, uu____2124) in
                     FStar_Pervasives_Native.Some uu____2113
                   else FStar_Pervasives_Native.None)
      | uu____2136 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2155 =
          let uu____2160 =
            let uu____2163 =
              let uu____2164 =
                let uu____2167 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2167 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2164) in
            inst_tscheme uu____2163 in
          (uu____2160, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____2155
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2181,uu____2182) ->
        let uu____2185 =
          let uu____2190 =
            let uu____2193 =
              let uu____2194 =
                let uu____2197 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2197 in
              (us, uu____2194) in
            inst_tscheme uu____2193 in
          (uu____2190, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____2185
    | uu____2208 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2243 =
        match uu____2243 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2293,uvs,t,uu____2296,uu____2297,uu____2298);
                    FStar_Syntax_Syntax.sigrng = uu____2299;
                    FStar_Syntax_Syntax.sigquals = uu____2300;
                    FStar_Syntax_Syntax.sigmeta = uu____2301;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____2311 =
                   let uu____2316 = inst_tscheme (uvs, t) in
                   (uu____2316, rng) in
                 FStar_Pervasives_Native.Some uu____2311
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2328;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2330;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____2338 =
                   let uu____2339 = in_cur_mod env l in uu____2339 = Yes in
                 if uu____2338
                 then
                   let uu____2345 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2345
                    then
                      let uu____2352 =
                        let uu____2357 = inst_tscheme (uvs, t) in
                        (uu____2357, rng) in
                      FStar_Pervasives_Native.Some uu____2352
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____2372 =
                      let uu____2377 = inst_tscheme (uvs, t) in
                      (uu____2377, rng) in
                    FStar_Pervasives_Native.Some uu____2372)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2390,uu____2391);
                    FStar_Syntax_Syntax.sigrng = uu____2392;
                    FStar_Syntax_Syntax.sigquals = uu____2393;
                    FStar_Syntax_Syntax.sigmeta = uu____2394;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2413 =
                        let uu____2418 = inst_tscheme (uvs, k) in
                        (uu____2418, rng) in
                      FStar_Pervasives_Native.Some uu____2413
                  | uu____2427 ->
                      let uu____2428 =
                        let uu____2433 =
                          let uu____2436 =
                            let uu____2437 =
                              let uu____2440 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2440 in
                            (uvs, uu____2437) in
                          inst_tscheme uu____2436 in
                        (uu____2433, rng) in
                      FStar_Pervasives_Native.Some uu____2428)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2455,uu____2456);
                    FStar_Syntax_Syntax.sigrng = uu____2457;
                    FStar_Syntax_Syntax.sigquals = uu____2458;
                    FStar_Syntax_Syntax.sigmeta = uu____2459;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2479 =
                        let uu____2484 = inst_tscheme_with (uvs, k) us in
                        (uu____2484, rng) in
                      FStar_Pervasives_Native.Some uu____2479
                  | uu____2493 ->
                      let uu____2494 =
                        let uu____2499 =
                          let uu____2502 =
                            let uu____2503 =
                              let uu____2506 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2506 in
                            (uvs, uu____2503) in
                          inst_tscheme_with uu____2502 us in
                        (uu____2499, rng) in
                      FStar_Pervasives_Native.Some uu____2494)
             | FStar_Util.Inr se ->
                 let uu____2526 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2537;
                        FStar_Syntax_Syntax.sigrng = uu____2538;
                        FStar_Syntax_Syntax.sigquals = uu____2539;
                        FStar_Syntax_Syntax.sigmeta = uu____2540;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____2549 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____2526
                   (FStar_Util.map_option
                      (fun uu____2572  ->
                         match uu____2572 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2589 =
        let uu____2595 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2595 mapper in
      match uu____2589 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___116_2647 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___116_2647.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___116_2647.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___116_2647.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2668 = lookup_qname env l in
      match uu____2668 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____2688 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2716 = try_lookup_bv env bv in
      match uu____2716 with
      | FStar_Pervasives_Native.None  ->
          let uu____2724 =
            let uu____2725 =
              let uu____2728 = variable_not_found bv in (uu____2728, bvr) in
            FStar_Errors.Error uu____2725 in
          raise uu____2724
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____2735 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2736 = FStar_Range.set_use_range r bvr in
          (uu____2735, uu____2736)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2748 = try_lookup_lid_aux env l in
      match uu____2748 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2790 =
            let uu____2795 =
              let uu____2798 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2798) in
            (uu____2795, r1) in
          FStar_Pervasives_Native.Some uu____2790
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____2815 = try_lookup_lid env l in
      match uu____2815 with
      | FStar_Pervasives_Native.None  ->
          let uu____2829 =
            let uu____2830 =
              let uu____2833 = name_not_found l in
              (uu____2833, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2830 in
          raise uu____2829
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___102_2854  ->
              match uu___102_2854 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2856 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____2867 = lookup_qname env lid in
      match uu____2867 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2882,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2885;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2887;_},FStar_Pervasives_Native.None
            ),uu____2888)
          ->
          let uu____2912 =
            let uu____2918 =
              let uu____2921 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2921) in
            (uu____2918, q) in
          FStar_Pervasives_Native.Some uu____2912
      | uu____2930 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____2952 = lookup_qname env lid in
      match uu____2952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2965,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2968;
              FStar_Syntax_Syntax.sigquals = uu____2969;
              FStar_Syntax_Syntax.sigmeta = uu____2970;_},FStar_Pervasives_Native.None
            ),uu____2971)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2995 ->
          let uu____3006 =
            let uu____3007 =
              let uu____3010 = name_not_found lid in
              (uu____3010, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3007 in
          raise uu____3006
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____3021 = lookup_qname env lid in
      match uu____3021 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3034,uvs,t,uu____3037,uu____3038,uu____3039);
              FStar_Syntax_Syntax.sigrng = uu____3040;
              FStar_Syntax_Syntax.sigquals = uu____3041;
              FStar_Syntax_Syntax.sigmeta = uu____3042;_},FStar_Pervasives_Native.None
            ),uu____3043)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3069 ->
          let uu____3080 =
            let uu____3081 =
              let uu____3084 = name_not_found lid in
              (uu____3084, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3081 in
          raise uu____3080
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____3096 = lookup_qname env lid in
      match uu____3096 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3110,uu____3111,uu____3112,uu____3113,uu____3114,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3116;
              FStar_Syntax_Syntax.sigquals = uu____3117;
              FStar_Syntax_Syntax.sigmeta = uu____3118;_},uu____3119),uu____3120)
          -> (true, dcs)
      | uu____3150 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3168 = lookup_qname env lid in
      match uu____3168 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3179,uu____3180,uu____3181,l,uu____3183,uu____3184);
              FStar_Syntax_Syntax.sigrng = uu____3185;
              FStar_Syntax_Syntax.sigquals = uu____3186;
              FStar_Syntax_Syntax.sigmeta = uu____3187;_},uu____3188),uu____3189)
          -> l
      | uu____3216 ->
          let uu____3227 =
            let uu____3228 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3228 in
          failwith uu____3227
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
        let uu____3252 = lookup_qname env lid in
        match uu____3252 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____3267) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3293,lbs),uu____3295,uu____3296) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3313 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3313
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____3334 -> FStar_Pervasives_Native.None)
        | uu____3337 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____3358 = lookup_qname env ftv in
      match uu____3358 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____3371) ->
          let uu____3394 = effect_signature se in
          (match uu____3394 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____3405,t),r) ->
               let uu____3414 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____3414)
      | uu____3415 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3432 = try_lookup_effect_lid env ftv in
      match uu____3432 with
      | FStar_Pervasives_Native.None  ->
          let uu____3434 =
            let uu____3435 =
              let uu____3438 = name_not_found ftv in
              (uu____3438, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3435 in
          raise uu____3434
      | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3452 = lookup_qname env lid0 in
        match uu____3452 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3470);
                FStar_Syntax_Syntax.sigrng = uu____3471;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3473;_},FStar_Pervasives_Native.None
              ),uu____3474)
            ->
            let lid1 =
              let uu____3501 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3501 in
            let uu____3502 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_3504  ->
                      match uu___103_3504 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3505 -> false)) in
            if uu____3502
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3518 =
                      let uu____3519 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3520 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3519 uu____3520 in
                    failwith uu____3518) in
               match (binders, univs1) with
               | ([],uu____3526) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3535,uu____3536::uu____3537::uu____3538) ->
                   let uu____3541 =
                     let uu____3542 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3543 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3542 uu____3543 in
                   failwith uu____3541
               | uu____3549 ->
                   let uu____3552 =
                     let uu____3555 =
                       let uu____3556 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3556) in
                     inst_tscheme_with uu____3555 insts in
                   (match uu____3552 with
                    | (uu____3564,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3567 =
                          let uu____3568 = FStar_Syntax_Subst.compress t1 in
                          uu____3568.FStar_Syntax_Syntax.n in
                        (match uu____3567 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____3598 -> failwith "Impossible")))
        | uu____3602 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3628 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3628 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____3635,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3640 = find1 l2 in
            (match uu____3640 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____3645 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3645 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____3648 = find1 l in
            (match uu____3648 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3660 = lookup_qname env l1 in
      match uu____3660 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3672;
              FStar_Syntax_Syntax.sigrng = uu____3673;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3675;_},uu____3676),uu____3677)
          -> q
      | uu____3702 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3725 =
          let uu____3726 =
            let uu____3727 = FStar_Util.string_of_int i in
            let uu____3728 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3727 uu____3728 in
          failwith uu____3726 in
        let uu____3729 = lookup_datacon env lid in
        match uu____3729 with
        | (uu____3732,t) ->
            let uu____3734 =
              let uu____3735 = FStar_Syntax_Subst.compress t in
              uu____3735.FStar_Syntax_Syntax.n in
            (match uu____3734 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3739) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3760 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____3760
                      FStar_Pervasives_Native.fst)
             | uu____3765 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3772 = lookup_qname env l in
      match uu____3772 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3783,uu____3784,uu____3785);
              FStar_Syntax_Syntax.sigrng = uu____3786;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3788;_},uu____3789),uu____3790)
          ->
          FStar_Util.for_some
            (fun uu___104_3815  ->
               match uu___104_3815 with
               | FStar_Syntax_Syntax.Projector uu____3816 -> true
               | uu____3819 -> false) quals
      | uu____3820 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3837 = lookup_qname env lid in
      match uu____3837 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3848,uu____3849,uu____3850,uu____3851,uu____3852,uu____3853);
              FStar_Syntax_Syntax.sigrng = uu____3854;
              FStar_Syntax_Syntax.sigquals = uu____3855;
              FStar_Syntax_Syntax.sigmeta = uu____3856;_},uu____3857),uu____3858)
          -> true
      | uu____3885 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3902 = lookup_qname env lid in
      match uu____3902 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3913,uu____3914,uu____3915,uu____3916,uu____3917,uu____3918);
              FStar_Syntax_Syntax.sigrng = uu____3919;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3921;_},uu____3922),uu____3923)
          ->
          FStar_Util.for_some
            (fun uu___105_3952  ->
               match uu___105_3952 with
               | FStar_Syntax_Syntax.RecordType uu____3953 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3958 -> true
               | uu____3963 -> false) quals
      | uu____3964 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3981 = lookup_qname env lid in
      match uu____3981 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3992,uu____3993,uu____3994);
              FStar_Syntax_Syntax.sigrng = uu____3995;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3997;_},uu____3998),uu____3999)
          ->
          FStar_Util.for_some
            (fun uu___106_4028  ->
               match uu___106_4028 with
               | FStar_Syntax_Syntax.Action uu____4029 -> true
               | uu____4030 -> false) quals
      | uu____4031 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____4050 =
        let uu____4051 = FStar_Syntax_Util.un_uinst head1 in
        uu____4051.FStar_Syntax_Syntax.n in
      match uu____4050 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4055 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____4093 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____4102) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4111 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4115 ->
                 FStar_Pervasives_Native.Some true
             | uu____4124 -> FStar_Pervasives_Native.Some false) in
      let uu____4125 =
        let uu____4127 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4127 mapper in
      match uu____4125 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4154 = lookup_qname env lid in
      match uu____4154 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4165,uu____4166,tps,uu____4168,uu____4169,uu____4170);
              FStar_Syntax_Syntax.sigrng = uu____4171;
              FStar_Syntax_Syntax.sigquals = uu____4172;
              FStar_Syntax_Syntax.sigmeta = uu____4173;_},uu____4174),uu____4175)
          -> FStar_List.length tps
      | uu____4207 ->
          let uu____4218 =
            let uu____4219 =
              let uu____4222 = name_not_found lid in
              (uu____4222, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4219 in
          raise uu____4218
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4244  ->
              match uu____4244 with
              | (d,uu____4249) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4258 = effect_decl_opt env l in
      match uu____4258 with
      | FStar_Pervasives_Native.None  ->
          let uu____4266 =
            let uu____4267 =
              let uu____4270 = name_not_found l in
              (uu____4270, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4267 in
          raise uu____4266
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some (fun t  -> fun wp  -> fun e  -> e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____4313 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4337  ->
                       match uu____4337 with
                       | (m1,m2,uu____4345,uu____4346,uu____4347) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4313 with
             | FStar_Pervasives_Native.None  ->
                 let uu____4356 =
                   let uu____4357 =
                     let uu____4360 =
                       let uu____4361 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4362 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4361
                         uu____4362 in
                     (uu____4360, (env.range)) in
                   FStar_Errors.Error uu____4357 in
                 raise uu____4356
             | FStar_Pervasives_Native.Some (uu____4366,uu____4367,m3,j1,j2)
                 -> (m3, j1, j2))
let monad_leq:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux decls m =
  let uu____4414 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4426  ->
            match uu____4426 with
            | (d,uu____4430) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4414 with
  | FStar_Pervasives_Native.None  ->
      let uu____4437 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4437
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____4446 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4446 with
       | (uu____4453,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4461)::(wp,uu____4463)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4485 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple2
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
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
            then
              FStar_Syntax_Syntax.mk_GTotal' res_t
                (FStar_Pervasives_Native.Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____4521 = get_range env in
                 let uu____4522 =
                   let uu____4525 =
                     let uu____4526 =
                       let uu____4536 =
                         let uu____4538 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4538] in
                       (null_wp, uu____4536) in
                     FStar_Syntax_Syntax.Tm_app uu____4526 in
                   FStar_Syntax_Syntax.mk uu____4525 in
                 uu____4522 FStar_Pervasives_Native.None uu____4521 in
               let uu____4548 =
                 let uu____4549 =
                   let uu____4555 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4555] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4549;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4548)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___117_4564 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___117_4564.order);
              joins = (uu___117_4564.joins)
            } in
          let uu___118_4569 = env in
          {
            solver = (uu___118_4569.solver);
            range = (uu___118_4569.range);
            curmodule = (uu___118_4569.curmodule);
            gamma = (uu___118_4569.gamma);
            gamma_cache = (uu___118_4569.gamma_cache);
            modules = (uu___118_4569.modules);
            expected_typ = (uu___118_4569.expected_typ);
            sigtab = (uu___118_4569.sigtab);
            is_pattern = (uu___118_4569.is_pattern);
            instantiate_imp = (uu___118_4569.instantiate_imp);
            effects;
            generalize = (uu___118_4569.generalize);
            letrecs = (uu___118_4569.letrecs);
            top_level = (uu___118_4569.top_level);
            check_uvars = (uu___118_4569.check_uvars);
            use_eq = (uu___118_4569.use_eq);
            is_iface = (uu___118_4569.is_iface);
            admit = (uu___118_4569.admit);
            lax = (uu___118_4569.lax);
            lax_universes = (uu___118_4569.lax_universes);
            type_of = (uu___118_4569.type_of);
            universe_of = (uu___118_4569.universe_of);
            use_bv_sorts = (uu___118_4569.use_bv_sorts);
            qname_and_index = (uu___118_4569.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4586 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4586 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4665 = (e1.mlift).mlift_wp t wp in
                              let uu____4666 = l1 t wp e in
                              l2 t uu____4665 uu____4666))
                | uu____4667 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4702 = inst_tscheme lift_t in
            match uu____4702 with
            | (uu____4707,lift_t1) ->
                let uu____4709 =
                  let uu____4712 =
                    let uu____4713 =
                      let uu____4723 =
                        let uu____4725 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4726 =
                          let uu____4728 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4728] in
                        uu____4725 :: uu____4726 in
                      (lift_t1, uu____4723) in
                    FStar_Syntax_Syntax.Tm_app uu____4713 in
                  FStar_Syntax_Syntax.mk uu____4712 in
                uu____4709 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4773 = inst_tscheme lift_t in
            match uu____4773 with
            | (uu____4778,lift_t1) ->
                let uu____4780 =
                  let uu____4783 =
                    let uu____4784 =
                      let uu____4794 =
                        let uu____4796 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4797 =
                          let uu____4799 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4800 =
                            let uu____4802 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4802] in
                          uu____4799 :: uu____4800 in
                        uu____4796 :: uu____4797 in
                      (lift_t1, uu____4794) in
                    FStar_Syntax_Syntax.Tm_app uu____4784 in
                  FStar_Syntax_Syntax.mk uu____4783 in
                uu____4780 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
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
              let uu____4843 =
                let uu____4844 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4844
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____4843 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4848 =
              let uu____4849 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4849 in
            let uu____4850 =
              let uu____4851 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4866 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4866) in
              FStar_Util.dflt "none" uu____4851 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4848
              uu____4850 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4879  ->
                    match uu____4879 with
                    | (e,uu____4884) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4897 =
            match uu____4897 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____4922 =
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
                                    (let uu____4934 =
                                       let uu____4939 =
                                         find_edge order1 (i, k) in
                                       let uu____4941 =
                                         find_edge order1 (k, j) in
                                       (uu____4939, uu____4941) in
                                     match uu____4934 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____4950 = compose_edges e1 e2 in
                                         [uu____4950]
                                     | uu____4951 -> []))))) in
              FStar_List.append order1 uu____4922 in
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
                   let uu____4966 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____4967 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4967
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4966
                   then
                     let uu____4970 =
                       let uu____4971 =
                         let uu____4974 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4975 = get_range env in
                         (uu____4974, uu____4975) in
                       FStar_Errors.Error uu____4971 in
                     raise uu____4970
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
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____5038 =
                                              let uu____5043 =
                                                find_edge order2 (i, k) in
                                              let uu____5045 =
                                                find_edge order2 (j, k) in
                                              (uu____5043, uu____5045) in
                                            match uu____5038 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____5068,uu____5069)
                                                     ->
                                                     let uu____5073 =
                                                       let uu____5076 =
                                                         let uu____5077 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5077 in
                                                       let uu____5079 =
                                                         let uu____5080 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5080 in
                                                       (uu____5076,
                                                         uu____5079) in
                                                     (match uu____5073 with
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
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____5099 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___119_5138 = env.effects in
              { decls = (uu___119_5138.decls); order = order2; joins } in
            let uu___120_5139 = env in
            {
              solver = (uu___120_5139.solver);
              range = (uu___120_5139.range);
              curmodule = (uu___120_5139.curmodule);
              gamma = (uu___120_5139.gamma);
              gamma_cache = (uu___120_5139.gamma_cache);
              modules = (uu___120_5139.modules);
              expected_typ = (uu___120_5139.expected_typ);
              sigtab = (uu___120_5139.sigtab);
              is_pattern = (uu___120_5139.is_pattern);
              instantiate_imp = (uu___120_5139.instantiate_imp);
              effects;
              generalize = (uu___120_5139.generalize);
              letrecs = (uu___120_5139.letrecs);
              top_level = (uu___120_5139.top_level);
              check_uvars = (uu___120_5139.check_uvars);
              use_eq = (uu___120_5139.use_eq);
              is_iface = (uu___120_5139.is_iface);
              admit = (uu___120_5139.admit);
              lax = (uu___120_5139.lax);
              lax_universes = (uu___120_5139.lax_universes);
              type_of = (uu___120_5139.type_of);
              universe_of = (uu___120_5139.universe_of);
              use_bv_sorts = (uu___120_5139.use_bv_sorts);
              qname_and_index = (uu___120_5139.qname_and_index)
            }))
      | uu____5140 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____5162 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5170 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5170 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____5180 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5180 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5197 =
                     let uu____5198 =
                       let uu____5201 =
                         let uu____5202 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5208 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5216 =
                           let uu____5217 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5217 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5202 uu____5208 uu____5216 in
                       (uu____5201, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5198 in
                   raise uu____5197)
                else ();
                (let inst1 =
                   let uu____5221 =
                     let uu____5227 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5227 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5234  ->
                        fun uu____5235  ->
                          match (uu____5234, uu____5235) with
                          | ((x,uu____5249),(t,uu____5251)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5221 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5266 =
                     let uu___121_5267 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___121_5267.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___121_5267.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___121_5267.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___121_5267.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5266
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5297 =
    let uu____5302 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5302 in
  match uu____5297 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____5318 =
        only_reifiable &&
          (let uu____5319 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5319) in
      if uu____5318
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____5332 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5334 =
               let uu____5343 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5343) in
             (match uu____5334 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5377 =
                    let uu____5380 = get_range env in
                    let uu____5381 =
                      let uu____5384 =
                        let uu____5385 =
                          let uu____5395 =
                            let uu____5397 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5397; wp] in
                          (repr, uu____5395) in
                        FStar_Syntax_Syntax.Tm_app uu____5385 in
                      FStar_Syntax_Syntax.mk uu____5384 in
                    uu____5381 FStar_Pervasives_Native.None uu____5380 in
                  FStar_Pervasives_Native.Some uu____5377))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
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
          let uu____5441 =
            let uu____5442 =
              let uu____5445 =
                let uu____5446 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5446 in
              let uu____5447 = get_range env in (uu____5445, uu____5447) in
            FStar_Errors.Error uu____5442 in
          raise uu____5441 in
        let uu____5448 = effect_repr_aux true env c u_c in
        match uu____5448 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
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
        | FStar_Util.Inr (eff_name,uu____5480) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5493 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5500 =
        let uu____5501 = FStar_Syntax_Subst.compress t in
        uu____5501.FStar_Syntax_Syntax.n in
      match uu____5500 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5504,c) ->
          is_reifiable_comp env c
      | uu____5516 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5534)::uu____5535 -> x :: rest
        | (Binding_sig_inst uu____5540)::uu____5541 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5550 = push1 x rest1 in local :: uu____5550 in
      let uu___122_5552 = env in
      let uu____5553 = push1 s env.gamma in
      {
        solver = (uu___122_5552.solver);
        range = (uu___122_5552.range);
        curmodule = (uu___122_5552.curmodule);
        gamma = uu____5553;
        gamma_cache = (uu___122_5552.gamma_cache);
        modules = (uu___122_5552.modules);
        expected_typ = (uu___122_5552.expected_typ);
        sigtab = (uu___122_5552.sigtab);
        is_pattern = (uu___122_5552.is_pattern);
        instantiate_imp = (uu___122_5552.instantiate_imp);
        effects = (uu___122_5552.effects);
        generalize = (uu___122_5552.generalize);
        letrecs = (uu___122_5552.letrecs);
        top_level = (uu___122_5552.top_level);
        check_uvars = (uu___122_5552.check_uvars);
        use_eq = (uu___122_5552.use_eq);
        is_iface = (uu___122_5552.is_iface);
        admit = (uu___122_5552.admit);
        lax = (uu___122_5552.lax);
        lax_universes = (uu___122_5552.lax_universes);
        type_of = (uu___122_5552.type_of);
        universe_of = (uu___122_5552.universe_of);
        use_bv_sorts = (uu___122_5552.use_bv_sorts);
        qname_and_index = (uu___122_5552.qname_and_index)
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
      let uu___123_5580 = env in
      {
        solver = (uu___123_5580.solver);
        range = (uu___123_5580.range);
        curmodule = (uu___123_5580.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___123_5580.gamma_cache);
        modules = (uu___123_5580.modules);
        expected_typ = (uu___123_5580.expected_typ);
        sigtab = (uu___123_5580.sigtab);
        is_pattern = (uu___123_5580.is_pattern);
        instantiate_imp = (uu___123_5580.instantiate_imp);
        effects = (uu___123_5580.effects);
        generalize = (uu___123_5580.generalize);
        letrecs = (uu___123_5580.letrecs);
        top_level = (uu___123_5580.top_level);
        check_uvars = (uu___123_5580.check_uvars);
        use_eq = (uu___123_5580.use_eq);
        is_iface = (uu___123_5580.is_iface);
        admit = (uu___123_5580.admit);
        lax = (uu___123_5580.lax);
        lax_universes = (uu___123_5580.lax_universes);
        type_of = (uu___123_5580.type_of);
        universe_of = (uu___123_5580.universe_of);
        use_bv_sorts = (uu___123_5580.use_bv_sorts);
        qname_and_index = (uu___123_5580.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv:
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___124_5601 = env in
             {
               solver = (uu___124_5601.solver);
               range = (uu___124_5601.range);
               curmodule = (uu___124_5601.curmodule);
               gamma = rest;
               gamma_cache = (uu___124_5601.gamma_cache);
               modules = (uu___124_5601.modules);
               expected_typ = (uu___124_5601.expected_typ);
               sigtab = (uu___124_5601.sigtab);
               is_pattern = (uu___124_5601.is_pattern);
               instantiate_imp = (uu___124_5601.instantiate_imp);
               effects = (uu___124_5601.effects);
               generalize = (uu___124_5601.generalize);
               letrecs = (uu___124_5601.letrecs);
               top_level = (uu___124_5601.top_level);
               check_uvars = (uu___124_5601.check_uvars);
               use_eq = (uu___124_5601.use_eq);
               is_iface = (uu___124_5601.is_iface);
               admit = (uu___124_5601.admit);
               lax = (uu___124_5601.lax);
               lax_universes = (uu___124_5601.lax_universes);
               type_of = (uu___124_5601.type_of);
               universe_of = (uu___124_5601.universe_of);
               use_bv_sorts = (uu___124_5601.use_bv_sorts);
               qname_and_index = (uu___124_5601.qname_and_index)
             }))
    | uu____5602 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5615  ->
             match uu____5615 with | (x,uu____5619) -> push_bv env1 x) env bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,(FStar_Syntax_Syntax.term',
                                                FStar_Syntax_Syntax.term')
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___125_5639 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___125_5639.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___125_5639.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
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
      (let uu___126_5669 = env in
       {
         solver = (uu___126_5669.solver);
         range = (uu___126_5669.range);
         curmodule = (uu___126_5669.curmodule);
         gamma = [];
         gamma_cache = (uu___126_5669.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___126_5669.sigtab);
         is_pattern = (uu___126_5669.is_pattern);
         instantiate_imp = (uu___126_5669.instantiate_imp);
         effects = (uu___126_5669.effects);
         generalize = (uu___126_5669.generalize);
         letrecs = (uu___126_5669.letrecs);
         top_level = (uu___126_5669.top_level);
         check_uvars = (uu___126_5669.check_uvars);
         use_eq = (uu___126_5669.use_eq);
         is_iface = (uu___126_5669.is_iface);
         admit = (uu___126_5669.admit);
         lax = (uu___126_5669.lax);
         lax_universes = (uu___126_5669.lax_universes);
         type_of = (uu___126_5669.type_of);
         universe_of = (uu___126_5669.universe_of);
         use_bv_sorts = (uu___126_5669.use_bv_sorts);
         qname_and_index = (uu___126_5669.qname_and_index)
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
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____5693 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5693 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5709 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5709)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___127_5719 = env in
      {
        solver = (uu___127_5719.solver);
        range = (uu___127_5719.range);
        curmodule = (uu___127_5719.curmodule);
        gamma = (uu___127_5719.gamma);
        gamma_cache = (uu___127_5719.gamma_cache);
        modules = (uu___127_5719.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___127_5719.sigtab);
        is_pattern = (uu___127_5719.is_pattern);
        instantiate_imp = (uu___127_5719.instantiate_imp);
        effects = (uu___127_5719.effects);
        generalize = (uu___127_5719.generalize);
        letrecs = (uu___127_5719.letrecs);
        top_level = (uu___127_5719.top_level);
        check_uvars = (uu___127_5719.check_uvars);
        use_eq = false;
        is_iface = (uu___127_5719.is_iface);
        admit = (uu___127_5719.admit);
        lax = (uu___127_5719.lax);
        lax_universes = (uu___127_5719.lax_universes);
        type_of = (uu___127_5719.type_of);
        universe_of = (uu___127_5719.universe_of);
        use_bv_sorts = (uu___127_5719.use_bv_sorts);
        qname_and_index = (uu___127_5719.qname_and_index)
      }
let expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ:
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____5735 = expected_typ env_ in
    ((let uu___128_5738 = env_ in
      {
        solver = (uu___128_5738.solver);
        range = (uu___128_5738.range);
        curmodule = (uu___128_5738.curmodule);
        gamma = (uu___128_5738.gamma);
        gamma_cache = (uu___128_5738.gamma_cache);
        modules = (uu___128_5738.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___128_5738.sigtab);
        is_pattern = (uu___128_5738.is_pattern);
        instantiate_imp = (uu___128_5738.instantiate_imp);
        effects = (uu___128_5738.effects);
        generalize = (uu___128_5738.generalize);
        letrecs = (uu___128_5738.letrecs);
        top_level = (uu___128_5738.top_level);
        check_uvars = (uu___128_5738.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5738.is_iface);
        admit = (uu___128_5738.admit);
        lax = (uu___128_5738.lax);
        lax_universes = (uu___128_5738.lax_universes);
        type_of = (uu___128_5738.type_of);
        universe_of = (uu___128_5738.universe_of);
        use_bv_sorts = (uu___128_5738.use_bv_sorts);
        qname_and_index = (uu___128_5738.qname_and_index)
      }), uu____5735)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____5749 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___107_5753  ->
                    match uu___107_5753 with
                    | Binding_sig (uu____5755,se) -> [se]
                    | uu____5759 -> [])) in
          FStar_All.pipe_right uu____5749 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___129_5764 = env in
       {
         solver = (uu___129_5764.solver);
         range = (uu___129_5764.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___129_5764.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___129_5764.expected_typ);
         sigtab = (uu___129_5764.sigtab);
         is_pattern = (uu___129_5764.is_pattern);
         instantiate_imp = (uu___129_5764.instantiate_imp);
         effects = (uu___129_5764.effects);
         generalize = (uu___129_5764.generalize);
         letrecs = (uu___129_5764.letrecs);
         top_level = (uu___129_5764.top_level);
         check_uvars = (uu___129_5764.check_uvars);
         use_eq = (uu___129_5764.use_eq);
         is_iface = (uu___129_5764.is_iface);
         admit = (uu___129_5764.admit);
         lax = (uu___129_5764.lax);
         lax_universes = (uu___129_5764.lax_universes);
         type_of = (uu___129_5764.type_of);
         universe_of = (uu___129_5764.universe_of);
         use_bv_sorts = (uu___129_5764.use_bv_sorts);
         qname_and_index = (uu___129_5764.qname_and_index)
       })
let uvars_in_env:
  env ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5814)::tl1 -> aux out tl1
      | (Binding_lid (uu____5817,(uu____5818,t)))::tl1 ->
          let uu____5827 =
            let uu____5831 = FStar_Syntax_Free.uvars t in ext out uu____5831 in
          aux uu____5827 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5835;
            FStar_Syntax_Syntax.index = uu____5836;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5842 =
            let uu____5846 = FStar_Syntax_Free.uvars t in ext out uu____5846 in
          aux uu____5842 tl1
      | (Binding_sig uu____5850)::uu____5851 -> out
      | (Binding_sig_inst uu____5856)::uu____5857 -> out in
    aux no_uvs1 env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5894)::tl1 -> aux out tl1
      | (Binding_univ uu____5901)::tl1 -> aux out tl1
      | (Binding_lid (uu____5904,(uu____5905,t)))::tl1 ->
          let uu____5914 =
            let uu____5916 = FStar_Syntax_Free.univs t in ext out uu____5916 in
          aux uu____5914 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5918;
            FStar_Syntax_Syntax.index = uu____5919;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5925 =
            let uu____5927 = FStar_Syntax_Free.univs t in ext out uu____5927 in
          aux uu____5925 tl1
      | (Binding_sig uu____5929)::uu____5930 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5967)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5977 = FStar_Util.set_add uname out in aux uu____5977 tl1
      | (Binding_lid (uu____5979,(uu____5980,t)))::tl1 ->
          let uu____5989 =
            let uu____5991 = FStar_Syntax_Free.univnames t in
            ext out uu____5991 in
          aux uu____5989 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5993;
            FStar_Syntax_Syntax.index = uu____5994;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6000 =
            let uu____6002 = FStar_Syntax_Free.univnames t in
            ext out uu____6002 in
          aux uu____6000 tl1
      | (Binding_sig uu____6004)::uu____6005 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___108_6021  ->
            match uu___108_6021 with
            | Binding_var x -> [x]
            | Binding_lid uu____6024 -> []
            | Binding_sig uu____6027 -> []
            | Binding_univ uu____6031 -> []
            | Binding_sig_inst uu____6032 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6042 =
      let uu____6044 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6044
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6042 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6060 =
      let uu____6061 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___109_6065  ->
                match uu___109_6065 with
                | Binding_var x ->
                    let uu____6067 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6067
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6070) ->
                    let uu____6071 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6071
                | Binding_sig (ls,uu____6073) ->
                    let uu____6076 =
                      let uu____6077 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6077
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6076
                | Binding_sig_inst (ls,uu____6083,uu____6084) ->
                    let uu____6087 =
                      let uu____6088 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6088
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6087)) in
      FStar_All.pipe_right uu____6061 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6060 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6100 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6100
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6117  ->
                 fun uu____6118  ->
                   match (uu____6117, uu____6118) with
                   | ((b1,uu____6128),(b2,uu____6130)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___110_6173  ->
             match uu___110_6173 with
             | Binding_sig (lids,uu____6177) -> FStar_List.append lids keys
             | uu____6180 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6182  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6186  -> ());
    push = (fun uu____6187  -> ());
    pop = (fun uu____6188  -> ());
    mark = (fun uu____6189  -> ());
    reset_mark = (fun uu____6190  -> ());
    commit_mark = (fun uu____6191  -> ());
    encode_modul = (fun uu____6192  -> fun uu____6193  -> ());
    encode_sig = (fun uu____6194  -> fun uu____6195  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6202  -> fun uu____6203  -> fun uu____6204  -> ());
    is_trivial = (fun uu____6208  -> fun uu____6209  -> false);
    finish = (fun uu____6210  -> ());
    refresh = (fun uu____6211  -> ())
  }