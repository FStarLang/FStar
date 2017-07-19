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
    match projectee with | Binding_var _0 -> true | uu____43 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
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
    match projectee with | NoDelta  -> true | uu____178 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
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
      | (NoDelta ,uu____1114) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____1115,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____1116,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____1117 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____1130 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____1139 =
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
          let uu____1184 = new_gamma_cache () in
          let uu____1187 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1184;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____1187;
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
  fun uu____1261  ->
    let uu____1262 = FStar_ST.read query_indices in
    match uu____1262 with
    | [] -> failwith "Empty query indices!"
    | uu____1285 ->
        let uu____1294 =
          let uu____1303 =
            let uu____1310 = FStar_ST.read query_indices in
            FStar_List.hd uu____1310 in
          let uu____1333 = FStar_ST.read query_indices in uu____1303 ::
            uu____1333 in
        FStar_ST.write query_indices uu____1294
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1366  ->
    let uu____1367 = FStar_ST.read query_indices in
    match uu____1367 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____1426  ->
    match uu____1426 with
    | (l,n1) ->
        let uu____1433 = FStar_ST.read query_indices in
        (match uu____1433 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1490 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1507  ->
    let uu____1508 = FStar_ST.read query_indices in FStar_List.hd uu____1508
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1533  ->
    let uu____1534 = FStar_ST.read query_indices in
    match uu____1534 with
    | hd1::uu____1552::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1600 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1620 =
       let uu____1623 = FStar_ST.read stack in env :: uu____1623 in
     FStar_ST.write stack uu____1620);
    (let uu___111_1630 = env in
     let uu____1631 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1634 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___111_1630.solver);
       range = (uu___111_1630.range);
       curmodule = (uu___111_1630.curmodule);
       gamma = (uu___111_1630.gamma);
       gamma_cache = uu____1631;
       modules = (uu___111_1630.modules);
       expected_typ = (uu___111_1630.expected_typ);
       sigtab = uu____1634;
       is_pattern = (uu___111_1630.is_pattern);
       instantiate_imp = (uu___111_1630.instantiate_imp);
       effects = (uu___111_1630.effects);
       generalize = (uu___111_1630.generalize);
       letrecs = (uu___111_1630.letrecs);
       top_level = (uu___111_1630.top_level);
       check_uvars = (uu___111_1630.check_uvars);
       use_eq = (uu___111_1630.use_eq);
       is_iface = (uu___111_1630.is_iface);
       admit = (uu___111_1630.admit);
       lax = (uu___111_1630.lax);
       lax_universes = (uu___111_1630.lax_universes);
       type_of = (uu___111_1630.type_of);
       universe_of = (uu___111_1630.universe_of);
       use_bv_sorts = (uu___111_1630.use_bv_sorts);
       qname_and_index = (uu___111_1630.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1639  ->
    let uu____1640 = FStar_ST.read stack in
    match uu____1640 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1652 -> failwith "Impossible: Too many pops"
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
    (let uu____1685 = pop_stack () in ());
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
        let uu____1711 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1734  ->
                  match uu____1734 with
                  | (m,uu____1740) -> FStar_Ident.lid_equals l m)) in
        (match uu____1711 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___112_1747 = env in
               {
                 solver = (uu___112_1747.solver);
                 range = (uu___112_1747.range);
                 curmodule = (uu___112_1747.curmodule);
                 gamma = (uu___112_1747.gamma);
                 gamma_cache = (uu___112_1747.gamma_cache);
                 modules = (uu___112_1747.modules);
                 expected_typ = (uu___112_1747.expected_typ);
                 sigtab = (uu___112_1747.sigtab);
                 is_pattern = (uu___112_1747.is_pattern);
                 instantiate_imp = (uu___112_1747.instantiate_imp);
                 effects = (uu___112_1747.effects);
                 generalize = (uu___112_1747.generalize);
                 letrecs = (uu___112_1747.letrecs);
                 top_level = (uu___112_1747.top_level);
                 check_uvars = (uu___112_1747.check_uvars);
                 use_eq = (uu___112_1747.use_eq);
                 is_iface = (uu___112_1747.is_iface);
                 admit = (uu___112_1747.admit);
                 lax = (uu___112_1747.lax);
                 lax_universes = (uu___112_1747.lax_universes);
                 type_of = (uu___112_1747.type_of);
                 universe_of = (uu___112_1747.universe_of);
                 use_bv_sorts = (uu___112_1747.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next))
               }))
         | FStar_Pervasives_Native.Some (uu____1752,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1760 = env in
               {
                 solver = (uu___113_1760.solver);
                 range = (uu___113_1760.range);
                 curmodule = (uu___113_1760.curmodule);
                 gamma = (uu___113_1760.gamma);
                 gamma_cache = (uu___113_1760.gamma_cache);
                 modules = (uu___113_1760.modules);
                 expected_typ = (uu___113_1760.expected_typ);
                 sigtab = (uu___113_1760.sigtab);
                 is_pattern = (uu___113_1760.is_pattern);
                 instantiate_imp = (uu___113_1760.instantiate_imp);
                 effects = (uu___113_1760.effects);
                 generalize = (uu___113_1760.generalize);
                 letrecs = (uu___113_1760.letrecs);
                 top_level = (uu___113_1760.top_level);
                 check_uvars = (uu___113_1760.check_uvars);
                 use_eq = (uu___113_1760.use_eq);
                 is_iface = (uu___113_1760.is_iface);
                 admit = (uu___113_1760.admit);
                 lax = (uu___113_1760.lax);
                 lax_universes = (uu___113_1760.lax_universes);
                 type_of = (uu___113_1760.type_of);
                 universe_of = (uu___113_1760.universe_of);
                 use_bv_sorts = (uu___113_1760.use_bv_sorts);
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
        (let uu___114_1778 = e in
         {
           solver = (uu___114_1778.solver);
           range = r;
           curmodule = (uu___114_1778.curmodule);
           gamma = (uu___114_1778.gamma);
           gamma_cache = (uu___114_1778.gamma_cache);
           modules = (uu___114_1778.modules);
           expected_typ = (uu___114_1778.expected_typ);
           sigtab = (uu___114_1778.sigtab);
           is_pattern = (uu___114_1778.is_pattern);
           instantiate_imp = (uu___114_1778.instantiate_imp);
           effects = (uu___114_1778.effects);
           generalize = (uu___114_1778.generalize);
           letrecs = (uu___114_1778.letrecs);
           top_level = (uu___114_1778.top_level);
           check_uvars = (uu___114_1778.check_uvars);
           use_eq = (uu___114_1778.use_eq);
           is_iface = (uu___114_1778.is_iface);
           admit = (uu___114_1778.admit);
           lax = (uu___114_1778.lax);
           lax_universes = (uu___114_1778.lax_universes);
           type_of = (uu___114_1778.type_of);
           universe_of = (uu___114_1778.universe_of);
           use_bv_sorts = (uu___114_1778.use_bv_sorts);
           qname_and_index = (uu___114_1778.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___115_1796 = env in
      {
        solver = (uu___115_1796.solver);
        range = (uu___115_1796.range);
        curmodule = lid;
        gamma = (uu___115_1796.gamma);
        gamma_cache = (uu___115_1796.gamma_cache);
        modules = (uu___115_1796.modules);
        expected_typ = (uu___115_1796.expected_typ);
        sigtab = (uu___115_1796.sigtab);
        is_pattern = (uu___115_1796.is_pattern);
        instantiate_imp = (uu___115_1796.instantiate_imp);
        effects = (uu___115_1796.effects);
        generalize = (uu___115_1796.generalize);
        letrecs = (uu___115_1796.letrecs);
        top_level = (uu___115_1796.top_level);
        check_uvars = (uu___115_1796.check_uvars);
        use_eq = (uu___115_1796.use_eq);
        is_iface = (uu___115_1796.is_iface);
        admit = (uu___115_1796.admit);
        lax = (uu___115_1796.lax);
        lax_universes = (uu___115_1796.lax_universes);
        type_of = (uu___115_1796.type_of);
        universe_of = (uu___115_1796.universe_of);
        use_bv_sorts = (uu___115_1796.use_bv_sorts);
        qname_and_index = (uu___115_1796.qname_and_index)
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
    let uu____1820 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1820
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1823  ->
    let uu____1824 = FStar_Unionfind.fresh FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.U_unif uu____1824
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
      | ((formals,t),uu____1860) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1882 = FStar_Syntax_Subst.subst vs t in (us, uu____1882)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___99_1889  ->
    match uu___99_1889 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1912  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____1925 = inst_tscheme t in
      match uu____1925 with
      | (us,t1) ->
          let uu____1936 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1936)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1948  ->
          match uu____1948 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1963 =
                         let uu____1964 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1965 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1966 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1967 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1964 uu____1965 uu____1966 uu____1967 in
                       failwith uu____1963)
                    else ();
                    (let uu____1969 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____1969))
               | uu____1976 ->
                   let uu____1977 =
                     let uu____1978 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1978 in
                   failwith uu____1977)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1982 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1986 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1990 -> false
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
             | ([],uu____2024) -> Maybe
             | (uu____2031,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____2050 -> No in
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
          let uu____2155 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____2155 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___100_2196  ->
                   match uu___100_2196 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____2239 =
                           let uu____2258 =
                             let uu____2273 = inst_tscheme t in
                             FStar_Util.Inl uu____2273 in
                           (uu____2258, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____2239
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____2339,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____2341);
                                     FStar_Syntax_Syntax.sigrng = uu____2342;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____2343;
                                     FStar_Syntax_Syntax.sigmeta = uu____2344;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____2360 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____2360
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____2406 ->
                             FStar_Pervasives_Native.Some t
                         | uu____2413 -> cache t in
                       let uu____2414 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____2414 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____2489 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____2489 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____2575 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2655 = find_in_sigtab env lid in
         match uu____2655 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2754) ->
          add_sigelts env ses
      | uu____2763 ->
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
            | uu____2774 -> ()))
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
        (fun uu___101_2801  ->
           match uu___101_2801 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2825 -> FStar_Pervasives_Native.None)
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
          ((uu____2860,lb::[]),uu____2862,uu____2863) ->
          let uu____2880 =
            let uu____2889 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2900 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2889, uu____2900) in
          FStar_Pervasives_Native.Some uu____2880
      | FStar_Syntax_Syntax.Sig_let ((uu____2913,lbs),uu____2915,uu____2916)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2954 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2966 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2966
                   then
                     let uu____2977 =
                       let uu____2986 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2997 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2986, uu____2997) in
                     FStar_Pervasives_Native.Some uu____2977
                   else FStar_Pervasives_Native.None)
      | uu____3019 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____3052 =
          let uu____3061 =
            let uu____3066 =
              let uu____3067 =
                let uu____3072 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____3072 in
              ((ne.FStar_Syntax_Syntax.univs), uu____3067) in
            inst_tscheme uu____3066 in
          (uu____3061, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____3052
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____3096,uu____3097) ->
        let uu____3102 =
          let uu____3111 =
            let uu____3116 =
              let uu____3117 =
                let uu____3122 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____3122 in
              (us, uu____3117) in
            inst_tscheme uu____3116 in
          (uu____3111, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____3102
    | uu____3143 -> FStar_Pervasives_Native.None
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
      let mapper uu____3203 =
        match uu____3203 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____3299,uvs,t,uu____3302,uu____3303,uu____3304);
                    FStar_Syntax_Syntax.sigrng = uu____3305;
                    FStar_Syntax_Syntax.sigquals = uu____3306;
                    FStar_Syntax_Syntax.sigmeta = uu____3307;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____3326 =
                   let uu____3335 = inst_tscheme (uvs, t) in
                   (uu____3335, rng) in
                 FStar_Pervasives_Native.Some uu____3326
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____3355;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____3357;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____3372 =
                   let uu____3373 = in_cur_mod env l in uu____3373 = Yes in
                 if uu____3372
                 then
                   let uu____3384 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____3384
                    then
                      let uu____3397 =
                        let uu____3406 = inst_tscheme (uvs, t) in
                        (uu____3406, rng) in
                      FStar_Pervasives_Native.Some uu____3397
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____3433 =
                      let uu____3442 = inst_tscheme (uvs, t) in
                      (uu____3442, rng) in
                    FStar_Pervasives_Native.Some uu____3433)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____3463,uu____3464);
                    FStar_Syntax_Syntax.sigrng = uu____3465;
                    FStar_Syntax_Syntax.sigquals = uu____3466;
                    FStar_Syntax_Syntax.sigmeta = uu____3467;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____3504 =
                        let uu____3513 = inst_tscheme (uvs, k) in
                        (uu____3513, rng) in
                      FStar_Pervasives_Native.Some uu____3504
                  | uu____3530 ->
                      let uu____3531 =
                        let uu____3540 =
                          let uu____3545 =
                            let uu____3546 =
                              let uu____3551 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____3551 in
                            (uvs, uu____3546) in
                          inst_tscheme uu____3545 in
                        (uu____3540, rng) in
                      FStar_Pervasives_Native.Some uu____3531)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____3576,uu____3577);
                    FStar_Syntax_Syntax.sigrng = uu____3578;
                    FStar_Syntax_Syntax.sigquals = uu____3579;
                    FStar_Syntax_Syntax.sigmeta = uu____3580;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____3618 =
                        let uu____3627 = inst_tscheme_with (uvs, k) us in
                        (uu____3627, rng) in
                      FStar_Pervasives_Native.Some uu____3618
                  | uu____3644 ->
                      let uu____3645 =
                        let uu____3654 =
                          let uu____3659 =
                            let uu____3660 =
                              let uu____3665 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____3665 in
                            (uvs, uu____3660) in
                          inst_tscheme_with uu____3659 us in
                        (uu____3654, rng) in
                      FStar_Pervasives_Native.Some uu____3645)
             | FStar_Util.Inr se ->
                 let uu____3703 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____3724;
                        FStar_Syntax_Syntax.sigrng = uu____3725;
                        FStar_Syntax_Syntax.sigquals = uu____3726;
                        FStar_Syntax_Syntax.sigmeta = uu____3727;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____3744 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____3703
                   (FStar_Util.map_option
                      (fun uu____3789  ->
                         match uu____3789 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____3820 =
        let uu____3831 = lookup_qname env lid in
        FStar_Util.bind_opt uu____3831 mapper in
      match uu____3820 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___116_3931 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___116_3931.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___116_3931.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___116_3931.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3958 = lookup_qname env l in
      match uu____3958 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____3997 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____4045 = try_lookup_bv env bv in
      match uu____4045 with
      | FStar_Pervasives_Native.None  ->
          let uu____4060 =
            let uu____4061 =
              let uu____4066 = variable_not_found bv in (uu____4066, bvr) in
            FStar_Errors.Error uu____4061 in
          raise uu____4060
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____4077 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____4078 = FStar_Range.set_use_range r bvr in
          (uu____4077, uu____4078)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____4095 = try_lookup_lid_aux env l in
      match uu____4095 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____4173 =
            let uu____4182 =
              let uu____4187 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____4187) in
            (uu____4182, r1) in
          FStar_Pervasives_Native.Some uu____4173
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____4214 = try_lookup_lid env l in
      match uu____4214 with
      | FStar_Pervasives_Native.None  ->
          let uu____4241 =
            let uu____4242 =
              let uu____4247 = name_not_found l in
              (uu____4247, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4242 in
          raise uu____4241
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___102_4281  ->
              match uu___102_4281 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____4283 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____4298 = lookup_qname env lid in
      match uu____4298 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____4327,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____4330;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____4332;_},FStar_Pervasives_Native.None
            ),uu____4333)
          ->
          let uu____4380 =
            let uu____4391 =
              let uu____4396 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____4396) in
            (uu____4391, q) in
          FStar_Pervasives_Native.Some uu____4380
      | uu____4413 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____4450 = lookup_qname env lid in
      match uu____4450 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____4475,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____4478;
              FStar_Syntax_Syntax.sigquals = uu____4479;
              FStar_Syntax_Syntax.sigmeta = uu____4480;_},FStar_Pervasives_Native.None
            ),uu____4481)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____4528 ->
          let uu____4549 =
            let uu____4550 =
              let uu____4555 = name_not_found lid in
              (uu____4555, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4550 in
          raise uu____4549
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____4570 = lookup_qname env lid in
      match uu____4570 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____4595,uvs,t,uu____4598,uu____4599,uu____4600);
              FStar_Syntax_Syntax.sigrng = uu____4601;
              FStar_Syntax_Syntax.sigquals = uu____4602;
              FStar_Syntax_Syntax.sigmeta = uu____4603;_},FStar_Pervasives_Native.None
            ),uu____4604)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____4655 ->
          let uu____4676 =
            let uu____4677 =
              let uu____4682 = name_not_found lid in
              (uu____4682, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4677 in
          raise uu____4676
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____4699 = lookup_qname env lid in
      match uu____4699 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4726,uu____4727,uu____4728,uu____4729,uu____4730,dcs);
              FStar_Syntax_Syntax.sigrng = uu____4732;
              FStar_Syntax_Syntax.sigquals = uu____4733;
              FStar_Syntax_Syntax.sigmeta = uu____4734;_},uu____4735),uu____4736)
          -> (true, dcs)
      | uu____4795 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____4824 = lookup_qname env lid in
      match uu____4824 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____4845,uu____4846,uu____4847,l,uu____4849,uu____4850);
              FStar_Syntax_Syntax.sigrng = uu____4851;
              FStar_Syntax_Syntax.sigquals = uu____4852;
              FStar_Syntax_Syntax.sigmeta = uu____4853;_},uu____4854),uu____4855)
          -> l
      | uu____4908 ->
          let uu____4929 =
            let uu____4930 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____4930 in
          failwith uu____4929
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
        let uu____4963 = lookup_qname env lid in
        match uu____4963 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____4991) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____5042,lbs),uu____5044,uu____5045) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____5076 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____5076
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____5116 -> FStar_Pervasives_Native.None)
        | uu____5121 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____5156 = lookup_qname env ftv in
      match uu____5156 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____5180) ->
          let uu____5225 = effect_signature se in
          (match uu____5225 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____5246,t),r) ->
               let uu____5261 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____5261)
      | uu____5262 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____5289 = try_lookup_effect_lid env ftv in
      match uu____5289 with
      | FStar_Pervasives_Native.None  ->
          let uu____5292 =
            let uu____5293 =
              let uu____5298 = name_not_found ftv in
              (uu____5298, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____5293 in
          raise uu____5292
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
        let uu____5315 = lookup_qname env lid0 in
        match uu____5315 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____5346);
                FStar_Syntax_Syntax.sigrng = uu____5347;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____5349;_},FStar_Pervasives_Native.None
              ),uu____5350)
            ->
            let lid1 =
              let uu____5402 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____5402 in
            let uu____5403 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_5406  ->
                      match uu___103_5406 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____5407 -> false)) in
            if uu____5403
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____5421 =
                      let uu____5422 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____5423 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____5422 uu____5423 in
                    failwith uu____5421) in
               match (binders, univs1) with
               | ([],uu____5430) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____5447,uu____5448::uu____5449::uu____5450) ->
                   let uu____5455 =
                     let uu____5456 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____5457 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____5456 uu____5457 in
                   failwith uu____5455
               | uu____5464 ->
                   let uu____5469 =
                     let uu____5474 =
                       let uu____5475 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____5475) in
                     inst_tscheme_with uu____5474 insts in
                   (match uu____5469 with
                    | (uu____5490,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____5493 =
                          let uu____5494 = FStar_Syntax_Subst.compress t1 in
                          uu____5494.FStar_Syntax_Syntax.n in
                        (match uu____5493 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____5551 -> failwith "Impossible")))
        | uu____5558 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____5598 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____5598 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____5611,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____5618 = find1 l2 in
            (match uu____5618 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____5625 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____5625 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____5629 = find1 l in
            (match uu____5629 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____5643 = lookup_qname env l1 in
      match uu____5643 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____5666;
              FStar_Syntax_Syntax.sigrng = uu____5667;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5669;_},uu____5670),uu____5671)
          -> q
      | uu____5720 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____5753 =
          let uu____5754 =
            let uu____5755 = FStar_Util.string_of_int i in
            let uu____5756 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____5755 uu____5756 in
          failwith uu____5754 in
        let uu____5757 = lookup_datacon env lid in
        match uu____5757 with
        | (uu____5762,t) ->
            let uu____5764 =
              let uu____5765 = FStar_Syntax_Subst.compress t in
              uu____5765.FStar_Syntax_Syntax.n in
            (match uu____5764 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5771) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____5806 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____5806
                      FStar_Pervasives_Native.fst)
             | uu____5815 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5822 = lookup_qname env l in
      match uu____5822 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5843,uu____5844,uu____5845);
              FStar_Syntax_Syntax.sigrng = uu____5846;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____5848;_},uu____5849),uu____5850)
          ->
          FStar_Util.for_some
            (fun uu___104_5899  ->
               match uu___104_5899 with
               | FStar_Syntax_Syntax.Projector uu____5900 -> true
               | uu____5905 -> false) quals
      | uu____5906 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____5933 = lookup_qname env lid in
      match uu____5933 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5954,uu____5955,uu____5956,uu____5957,uu____5958,uu____5959);
              FStar_Syntax_Syntax.sigrng = uu____5960;
              FStar_Syntax_Syntax.sigquals = uu____5961;
              FStar_Syntax_Syntax.sigmeta = uu____5962;_},uu____5963),uu____5964)
          -> true
      | uu____6017 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6044 = lookup_qname env lid in
      match uu____6044 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6065,uu____6066,uu____6067,uu____6068,uu____6069,uu____6070);
              FStar_Syntax_Syntax.sigrng = uu____6071;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6073;_},uu____6074),uu____6075)
          ->
          FStar_Util.for_some
            (fun uu___105_6132  ->
               match uu___105_6132 with
               | FStar_Syntax_Syntax.RecordType uu____6133 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6142 -> true
               | uu____6151 -> false) quals
      | uu____6152 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6179 = lookup_qname env lid in
      match uu____6179 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6200,uu____6201,uu____6202);
              FStar_Syntax_Syntax.sigrng = uu____6203;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6205;_},uu____6206),uu____6207)
          ->
          FStar_Util.for_some
            (fun uu___106_6264  ->
               match uu___106_6264 with
               | FStar_Syntax_Syntax.Action uu____6265 -> true
               | uu____6266 -> false) quals
      | uu____6267 -> false
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
      let uu____6297 =
        let uu____6298 = FStar_Syntax_Util.un_uinst head1 in
        uu____6298.FStar_Syntax_Syntax.n in
      match uu____6297 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6304 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____6369 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____6385) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6402 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6409 ->
                 FStar_Pervasives_Native.Some true
             | uu____6426 -> FStar_Pervasives_Native.Some false) in
      let uu____6427 =
        let uu____6430 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6430 mapper in
      match uu____6427 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6476 = lookup_qname env lid in
      match uu____6476 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6497,uu____6498,tps,uu____6500,uu____6501,uu____6502);
              FStar_Syntax_Syntax.sigrng = uu____6503;
              FStar_Syntax_Syntax.sigquals = uu____6504;
              FStar_Syntax_Syntax.sigmeta = uu____6505;_},uu____6506),uu____6507)
          -> FStar_List.length tps
      | uu____6568 ->
          let uu____6589 =
            let uu____6590 =
              let uu____6595 = name_not_found lid in
              (uu____6595, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____6590 in
          raise uu____6589
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
           (fun uu____6632  ->
              match uu____6632 with
              | (d,uu____6640) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____6651 = effect_decl_opt env l in
      match uu____6651 with
      | FStar_Pervasives_Native.None  ->
          let uu____6666 =
            let uu____6667 =
              let uu____6672 = name_not_found l in
              (uu____6672, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____6667 in
          raise uu____6666
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
            (let uu____6734 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____6781  ->
                       match uu____6781 with
                       | (m1,m2,uu____6794,uu____6795,uu____6796) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____6734 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6813 =
                   let uu____6814 =
                     let uu____6819 =
                       let uu____6820 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____6821 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____6820
                         uu____6821 in
                     (uu____6819, (env.range)) in
                   FStar_Errors.Error uu____6814 in
                 raise uu____6813
             | FStar_Pervasives_Native.Some (uu____6828,uu____6829,m3,j1,j2)
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
  let uu____6896 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____6919  ->
            match uu____6919 with
            | (d,uu____6925) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____6896 with
  | FStar_Pervasives_Native.None  ->
      let uu____6938 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____6938
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____6953 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____6953 with
       | (uu____6966,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____6978)::(wp,uu____6980)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7022 -> failwith "Impossible"))
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
                 let uu____7069 = get_range env in
                 let uu____7070 =
                   let uu____7075 =
                     let uu____7076 =
                       let uu____7095 =
                         let uu____7098 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____7098] in
                       (null_wp, uu____7095) in
                     FStar_Syntax_Syntax.Tm_app uu____7076 in
                   FStar_Syntax_Syntax.mk uu____7075 in
                 uu____7070 FStar_Pervasives_Native.None uu____7069 in
               let uu____7105 =
                 let uu____7106 =
                   let uu____7117 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____7117] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7106;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____7105)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___117_7126 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___117_7126.order);
              joins = (uu___117_7126.joins)
            } in
          let uu___118_7135 = env in
          {
            solver = (uu___118_7135.solver);
            range = (uu___118_7135.range);
            curmodule = (uu___118_7135.curmodule);
            gamma = (uu___118_7135.gamma);
            gamma_cache = (uu___118_7135.gamma_cache);
            modules = (uu___118_7135.modules);
            expected_typ = (uu___118_7135.expected_typ);
            sigtab = (uu___118_7135.sigtab);
            is_pattern = (uu___118_7135.is_pattern);
            instantiate_imp = (uu___118_7135.instantiate_imp);
            effects;
            generalize = (uu___118_7135.generalize);
            letrecs = (uu___118_7135.letrecs);
            top_level = (uu___118_7135.top_level);
            check_uvars = (uu___118_7135.check_uvars);
            use_eq = (uu___118_7135.use_eq);
            is_iface = (uu___118_7135.is_iface);
            admit = (uu___118_7135.admit);
            lax = (uu___118_7135.lax);
            lax_universes = (uu___118_7135.lax_universes);
            type_of = (uu___118_7135.type_of);
            universe_of = (uu___118_7135.universe_of);
            use_bv_sorts = (uu___118_7135.use_bv_sorts);
            qname_and_index = (uu___118_7135.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7152 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____7152 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7237 = (e1.mlift).mlift_wp t wp in
                              let uu____7238 = l1 t wp e in
                              l2 t uu____7237 uu____7238))
                | uu____7239 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7280 = inst_tscheme lift_t in
            match uu____7280 with
            | (uu____7289,lift_t1) ->
                let uu____7291 =
                  let uu____7296 =
                    let uu____7297 =
                      let uu____7316 =
                        let uu____7319 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7320 =
                          let uu____7323 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7323] in
                        uu____7319 :: uu____7320 in
                      (lift_t1, uu____7316) in
                    FStar_Syntax_Syntax.Tm_app uu____7297 in
                  FStar_Syntax_Syntax.mk uu____7296 in
                uu____7291 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7373 = inst_tscheme lift_t in
            match uu____7373 with
            | (uu____7382,lift_t1) ->
                let uu____7384 =
                  let uu____7389 =
                    let uu____7390 =
                      let uu____7409 =
                        let uu____7412 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7413 =
                          let uu____7416 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7417 =
                            let uu____7420 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7420] in
                          uu____7416 :: uu____7417 in
                        uu____7412 :: uu____7413 in
                      (lift_t1, uu____7409) in
                    FStar_Syntax_Syntax.Tm_app uu____7390 in
                  FStar_Syntax_Syntax.mk uu____7389 in
                uu____7384 FStar_Pervasives_Native.None
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
              let uu____7463 =
                let uu____7464 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7464
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____7463 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7468 =
              let uu____7469 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7469 in
            let uu____7470 =
              let uu____7471 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7487 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7487) in
              FStar_Util.dflt "none" uu____7471 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7468
              uu____7470 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7510  ->
                    match uu____7510 with
                    | (e,uu____7518) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7537 =
            match uu____7537 with
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
              let uu____7574 =
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
                                    (let uu____7593 =
                                       let uu____7602 =
                                         find_edge order1 (i, k) in
                                       let uu____7605 =
                                         find_edge order1 (k, j) in
                                       (uu____7602, uu____7605) in
                                     match uu____7593 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____7620 = compose_edges e1 e2 in
                                         [uu____7620]
                                     | uu____7621 -> []))))) in
              FStar_List.append order1 uu____7574 in
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
                   let uu____7645 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____7646 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7646
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7645
                   then
                     let uu____7651 =
                       let uu____7652 =
                         let uu____7657 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7658 = get_range env in
                         (uu____7657, uu____7658) in
                       FStar_Errors.Error uu____7652 in
                     raise uu____7651
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
                                            let uu____7775 =
                                              let uu____7784 =
                                                find_edge order2 (i, k) in
                                              let uu____7787 =
                                                find_edge order2 (j, k) in
                                              (uu____7784, uu____7787) in
                                            match uu____7775 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____7829,uu____7830)
                                                     ->
                                                     let uu____7837 =
                                                       let uu____7842 =
                                                         let uu____7843 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7843 in
                                                       let uu____7846 =
                                                         let uu____7847 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7847 in
                                                       (uu____7842,
                                                         uu____7846) in
                                                     (match uu____7837 with
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
                                            | uu____7882 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___119_7955 = env.effects in
              { decls = (uu___119_7955.decls); order = order2; joins } in
            let uu___120_7956 = env in
            {
              solver = (uu___120_7956.solver);
              range = (uu___120_7956.range);
              curmodule = (uu___120_7956.curmodule);
              gamma = (uu___120_7956.gamma);
              gamma_cache = (uu___120_7956.gamma_cache);
              modules = (uu___120_7956.modules);
              expected_typ = (uu___120_7956.expected_typ);
              sigtab = (uu___120_7956.sigtab);
              is_pattern = (uu___120_7956.is_pattern);
              instantiate_imp = (uu___120_7956.instantiate_imp);
              effects;
              generalize = (uu___120_7956.generalize);
              letrecs = (uu___120_7956.letrecs);
              top_level = (uu___120_7956.top_level);
              check_uvars = (uu___120_7956.check_uvars);
              use_eq = (uu___120_7956.use_eq);
              is_iface = (uu___120_7956.is_iface);
              admit = (uu___120_7956.admit);
              lax = (uu___120_7956.lax);
              lax_universes = (uu___120_7956.lax_universes);
              type_of = (uu___120_7956.type_of);
              universe_of = (uu___120_7956.universe_of);
              use_bv_sorts = (uu___120_7956.use_bv_sorts);
              qname_and_index = (uu___120_7956.qname_and_index)
            }))
      | uu____7957 -> env
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
        | uu____7989 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____7997 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____7997 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____8014 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____8014 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____8034 =
                     let uu____8035 =
                       let uu____8040 =
                         let uu____8041 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____8046 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____8055 =
                           let uu____8056 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____8056 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8041 uu____8046 uu____8055 in
                       (uu____8040, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____8035 in
                   raise uu____8034)
                else ();
                (let inst1 =
                   let uu____8061 =
                     let uu____8072 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____8072 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____8085  ->
                        fun uu____8086  ->
                          match (uu____8085, uu____8086) with
                          | ((x,uu____8112),(t,uu____8114)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8061 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____8141 =
                     let uu___121_8142 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___121_8142.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___121_8142.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___121_8142.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___121_8142.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____8141
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____8179 =
    let uu____8188 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____8188 in
  match uu____8179 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____8217 =
        only_reifiable &&
          (let uu____8218 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____8218) in
      if uu____8217
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____8242 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____8244 =
               let uu____8261 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____8261) in
             (match uu____8244 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____8325 =
                    let uu____8330 = get_range env in
                    let uu____8331 =
                      let uu____8336 =
                        let uu____8337 =
                          let uu____8356 =
                            let uu____8359 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____8359; wp] in
                          (repr, uu____8356) in
                        FStar_Syntax_Syntax.Tm_app uu____8337 in
                      FStar_Syntax_Syntax.mk uu____8336 in
                    uu____8331 FStar_Pervasives_Native.None uu____8330 in
                  FStar_Pervasives_Native.Some uu____8325))
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
          let uu____8412 =
            let uu____8413 =
              let uu____8418 =
                let uu____8419 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8419 in
              let uu____8420 = get_range env in (uu____8418, uu____8420) in
            FStar_Errors.Error uu____8413 in
          raise uu____8412 in
        let uu____8421 = effect_repr_aux true env c u_c in
        match uu____8421 with
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
        | FStar_Util.Inr (eff_name,uu____8467) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____8485 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8492 =
        let uu____8493 = FStar_Syntax_Subst.compress t in
        uu____8493.FStar_Syntax_Syntax.n in
      match uu____8492 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8498,c) ->
          is_reifiable_comp env c
      | uu____8520 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8542)::uu____8543 -> x :: rest
        | (Binding_sig_inst uu____8552)::uu____8553 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8568 = push1 x rest1 in local :: uu____8568 in
      let uu___122_8571 = env in
      let uu____8572 = push1 s env.gamma in
      {
        solver = (uu___122_8571.solver);
        range = (uu___122_8571.range);
        curmodule = (uu___122_8571.curmodule);
        gamma = uu____8572;
        gamma_cache = (uu___122_8571.gamma_cache);
        modules = (uu___122_8571.modules);
        expected_typ = (uu___122_8571.expected_typ);
        sigtab = (uu___122_8571.sigtab);
        is_pattern = (uu___122_8571.is_pattern);
        instantiate_imp = (uu___122_8571.instantiate_imp);
        effects = (uu___122_8571.effects);
        generalize = (uu___122_8571.generalize);
        letrecs = (uu___122_8571.letrecs);
        top_level = (uu___122_8571.top_level);
        check_uvars = (uu___122_8571.check_uvars);
        use_eq = (uu___122_8571.use_eq);
        is_iface = (uu___122_8571.is_iface);
        admit = (uu___122_8571.admit);
        lax = (uu___122_8571.lax);
        lax_universes = (uu___122_8571.lax_universes);
        type_of = (uu___122_8571.type_of);
        universe_of = (uu___122_8571.universe_of);
        use_bv_sorts = (uu___122_8571.use_bv_sorts);
        qname_and_index = (uu___122_8571.qname_and_index)
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
      let uu___123_8602 = env in
      {
        solver = (uu___123_8602.solver);
        range = (uu___123_8602.range);
        curmodule = (uu___123_8602.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___123_8602.gamma_cache);
        modules = (uu___123_8602.modules);
        expected_typ = (uu___123_8602.expected_typ);
        sigtab = (uu___123_8602.sigtab);
        is_pattern = (uu___123_8602.is_pattern);
        instantiate_imp = (uu___123_8602.instantiate_imp);
        effects = (uu___123_8602.effects);
        generalize = (uu___123_8602.generalize);
        letrecs = (uu___123_8602.letrecs);
        top_level = (uu___123_8602.top_level);
        check_uvars = (uu___123_8602.check_uvars);
        use_eq = (uu___123_8602.use_eq);
        is_iface = (uu___123_8602.is_iface);
        admit = (uu___123_8602.admit);
        lax = (uu___123_8602.lax);
        lax_universes = (uu___123_8602.lax_universes);
        type_of = (uu___123_8602.type_of);
        universe_of = (uu___123_8602.universe_of);
        use_bv_sorts = (uu___123_8602.use_bv_sorts);
        qname_and_index = (uu___123_8602.qname_and_index)
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
            (let uu___124_8632 = env in
             {
               solver = (uu___124_8632.solver);
               range = (uu___124_8632.range);
               curmodule = (uu___124_8632.curmodule);
               gamma = rest;
               gamma_cache = (uu___124_8632.gamma_cache);
               modules = (uu___124_8632.modules);
               expected_typ = (uu___124_8632.expected_typ);
               sigtab = (uu___124_8632.sigtab);
               is_pattern = (uu___124_8632.is_pattern);
               instantiate_imp = (uu___124_8632.instantiate_imp);
               effects = (uu___124_8632.effects);
               generalize = (uu___124_8632.generalize);
               letrecs = (uu___124_8632.letrecs);
               top_level = (uu___124_8632.top_level);
               check_uvars = (uu___124_8632.check_uvars);
               use_eq = (uu___124_8632.use_eq);
               is_iface = (uu___124_8632.is_iface);
               admit = (uu___124_8632.admit);
               lax = (uu___124_8632.lax);
               lax_universes = (uu___124_8632.lax_universes);
               type_of = (uu___124_8632.type_of);
               universe_of = (uu___124_8632.universe_of);
               use_bv_sorts = (uu___124_8632.use_bv_sorts);
               qname_and_index = (uu___124_8632.qname_and_index)
             }))
    | uu____8633 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8651  ->
             match uu____8651 with | (x,uu____8657) -> push_bv env1 x) env bs
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
            let uu___125_8689 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___125_8689.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___125_8689.FStar_Syntax_Syntax.index);
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
      (let uu___126_8727 = env in
       {
         solver = (uu___126_8727.solver);
         range = (uu___126_8727.range);
         curmodule = (uu___126_8727.curmodule);
         gamma = [];
         gamma_cache = (uu___126_8727.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___126_8727.sigtab);
         is_pattern = (uu___126_8727.is_pattern);
         instantiate_imp = (uu___126_8727.instantiate_imp);
         effects = (uu___126_8727.effects);
         generalize = (uu___126_8727.generalize);
         letrecs = (uu___126_8727.letrecs);
         top_level = (uu___126_8727.top_level);
         check_uvars = (uu___126_8727.check_uvars);
         use_eq = (uu___126_8727.use_eq);
         is_iface = (uu___126_8727.is_iface);
         admit = (uu___126_8727.admit);
         lax = (uu___126_8727.lax);
         lax_universes = (uu___126_8727.lax_universes);
         type_of = (uu___126_8727.type_of);
         universe_of = (uu___126_8727.universe_of);
         use_bv_sorts = (uu___126_8727.use_bv_sorts);
         qname_and_index = (uu___126_8727.qname_and_index)
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
        let uu____8757 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8757 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8785 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8785)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___127_8798 = env in
      {
        solver = (uu___127_8798.solver);
        range = (uu___127_8798.range);
        curmodule = (uu___127_8798.curmodule);
        gamma = (uu___127_8798.gamma);
        gamma_cache = (uu___127_8798.gamma_cache);
        modules = (uu___127_8798.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___127_8798.sigtab);
        is_pattern = (uu___127_8798.is_pattern);
        instantiate_imp = (uu___127_8798.instantiate_imp);
        effects = (uu___127_8798.effects);
        generalize = (uu___127_8798.generalize);
        letrecs = (uu___127_8798.letrecs);
        top_level = (uu___127_8798.top_level);
        check_uvars = (uu___127_8798.check_uvars);
        use_eq = false;
        is_iface = (uu___127_8798.is_iface);
        admit = (uu___127_8798.admit);
        lax = (uu___127_8798.lax);
        lax_universes = (uu___127_8798.lax_universes);
        type_of = (uu___127_8798.type_of);
        universe_of = (uu___127_8798.universe_of);
        use_bv_sorts = (uu___127_8798.use_bv_sorts);
        qname_and_index = (uu___127_8798.qname_and_index)
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
    let uu____8822 = expected_typ env_ in
    ((let uu___128_8827 = env_ in
      {
        solver = (uu___128_8827.solver);
        range = (uu___128_8827.range);
        curmodule = (uu___128_8827.curmodule);
        gamma = (uu___128_8827.gamma);
        gamma_cache = (uu___128_8827.gamma_cache);
        modules = (uu___128_8827.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___128_8827.sigtab);
        is_pattern = (uu___128_8827.is_pattern);
        instantiate_imp = (uu___128_8827.instantiate_imp);
        effects = (uu___128_8827.effects);
        generalize = (uu___128_8827.generalize);
        letrecs = (uu___128_8827.letrecs);
        top_level = (uu___128_8827.top_level);
        check_uvars = (uu___128_8827.check_uvars);
        use_eq = false;
        is_iface = (uu___128_8827.is_iface);
        admit = (uu___128_8827.admit);
        lax = (uu___128_8827.lax);
        lax_universes = (uu___128_8827.lax_universes);
        type_of = (uu___128_8827.type_of);
        universe_of = (uu___128_8827.universe_of);
        use_bv_sorts = (uu___128_8827.use_bv_sorts);
        qname_and_index = (uu___128_8827.qname_and_index)
      }), uu____8822)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____8840 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___107_8847  ->
                    match uu___107_8847 with
                    | Binding_sig (uu____8850,se) -> [se]
                    | uu____8856 -> [])) in
          FStar_All.pipe_right uu____8840 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___129_8863 = env in
       {
         solver = (uu___129_8863.solver);
         range = (uu___129_8863.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___129_8863.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___129_8863.expected_typ);
         sigtab = (uu___129_8863.sigtab);
         is_pattern = (uu___129_8863.is_pattern);
         instantiate_imp = (uu___129_8863.instantiate_imp);
         effects = (uu___129_8863.effects);
         generalize = (uu___129_8863.generalize);
         letrecs = (uu___129_8863.letrecs);
         top_level = (uu___129_8863.top_level);
         check_uvars = (uu___129_8863.check_uvars);
         use_eq = (uu___129_8863.use_eq);
         is_iface = (uu___129_8863.is_iface);
         admit = (uu___129_8863.admit);
         lax = (uu___129_8863.lax);
         lax_universes = (uu___129_8863.lax_universes);
         type_of = (uu___129_8863.type_of);
         universe_of = (uu___129_8863.universe_of);
         use_bv_sorts = (uu___129_8863.use_bv_sorts);
         qname_and_index = (uu___129_8863.qname_and_index)
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
      | (Binding_univ uu____8944)::tl1 -> aux out tl1
      | (Binding_lid (uu____8948,(uu____8949,t)))::tl1 ->
          let uu____8964 =
            let uu____8971 = FStar_Syntax_Free.uvars t in ext out uu____8971 in
          aux uu____8964 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8978;
            FStar_Syntax_Syntax.index = uu____8979;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8988 =
            let uu____8995 = FStar_Syntax_Free.uvars t in ext out uu____8995 in
          aux uu____8988 tl1
      | (Binding_sig uu____9002)::uu____9003 -> out
      | (Binding_sig_inst uu____9012)::uu____9013 -> out in
    aux no_uvs1 env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____9068)::tl1 -> aux out tl1
      | (Binding_univ uu____9080)::tl1 -> aux out tl1
      | (Binding_lid (uu____9084,(uu____9085,t)))::tl1 ->
          let uu____9100 =
            let uu____9103 = FStar_Syntax_Free.univs t in ext out uu____9103 in
          aux uu____9100 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____9106;
            FStar_Syntax_Syntax.index = uu____9107;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____9116 =
            let uu____9119 = FStar_Syntax_Free.univs t in ext out uu____9119 in
          aux uu____9116 tl1
      | (Binding_sig uu____9122)::uu____9123 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____9176)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____9192 = FStar_Util.set_add uname out in aux uu____9192 tl1
      | (Binding_lid (uu____9195,(uu____9196,t)))::tl1 ->
          let uu____9211 =
            let uu____9214 = FStar_Syntax_Free.univnames t in
            ext out uu____9214 in
          aux uu____9211 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____9217;
            FStar_Syntax_Syntax.index = uu____9218;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____9227 =
            let uu____9230 = FStar_Syntax_Free.univnames t in
            ext out uu____9230 in
          aux uu____9227 tl1
      | (Binding_sig uu____9233)::uu____9234 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___108_9259  ->
            match uu___108_9259 with
            | Binding_var x -> [x]
            | Binding_lid uu____9263 -> []
            | Binding_sig uu____9268 -> []
            | Binding_univ uu____9275 -> []
            | Binding_sig_inst uu____9276 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____9292 =
      let uu____9295 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____9295
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____9292 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____9317 =
      let uu____9318 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___109_9325  ->
                match uu___109_9325 with
                | Binding_var x ->
                    let uu____9327 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____9327
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____9330) ->
                    let uu____9331 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____9331
                | Binding_sig (ls,uu____9333) ->
                    let uu____9338 =
                      let uu____9339 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9339
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____9338
                | Binding_sig_inst (ls,uu____9349,uu____9350) ->
                    let uu____9355 =
                      let uu____9356 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9356
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____9355)) in
      FStar_All.pipe_right uu____9318 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____9317 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____9373 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____9373
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____9395  ->
                 fun uu____9396  ->
                   match (uu____9395, uu____9396) with
                   | ((b1,uu____9414),(b2,uu____9416)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___110_9467  ->
             match uu___110_9467 with
             | Binding_sig (lids,uu____9473) -> FStar_List.append lids keys
             | uu____9478 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9481  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____9486  -> ());
    push = (fun uu____9487  -> ());
    pop = (fun uu____9488  -> ());
    mark = (fun uu____9489  -> ());
    reset_mark = (fun uu____9490  -> ());
    commit_mark = (fun uu____9491  -> ());
    encode_modul = (fun uu____9492  -> fun uu____9493  -> ());
    encode_sig = (fun uu____9494  -> fun uu____9495  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____9506  -> fun uu____9507  -> fun uu____9508  -> ());
    is_trivial = (fun uu____9513  -> fun uu____9514  -> false);
    finish = (fun uu____9515  -> ());
    refresh = (fun uu____9516  -> ())
  }