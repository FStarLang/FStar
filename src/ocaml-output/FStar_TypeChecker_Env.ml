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
  | UnfoldTac
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
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____157 -> false
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
type name_prefix = Prims.string Prims.list
type flat_proof_namespace = (name_prefix* Prims.bool) Prims.list
type proof_namespace = flat_proof_namespace Prims.list
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
  qname_and_index: (FStar_Ident.lident* Prims.int) option;
  proof_ns: proof_namespace;}
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
      | (NoDelta ,uu____946) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____947,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____948,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____949 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____959 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____967 =
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
          let uu____1006 = new_gamma_cache () in
          let uu____1008 = new_sigtab () in
          let uu____1010 =
            let uu____1011 = FStar_Options.using_facts_from () in
            match uu____1011 with
            | Some ns ->
                let uu____1017 =
                  let uu____1022 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____1022 [([], false)] in
                [uu____1017]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1006;
            modules = [];
            expected_typ = None;
            sigtab = uu____1008;
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
            qname_and_index = None;
            proof_ns = uu____1010
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1100  ->
    let uu____1101 = FStar_ST.read query_indices in
    match uu____1101 with
    | [] -> failwith "Empty query indices!"
    | uu____1115 ->
        let uu____1120 =
          let uu____1125 =
            let uu____1129 = FStar_ST.read query_indices in
            FStar_List.hd uu____1129 in
          let uu____1143 = FStar_ST.read query_indices in uu____1125 ::
            uu____1143 in
        FStar_ST.write query_indices uu____1120
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1165  ->
    let uu____1166 = FStar_ST.read query_indices in
    match uu____1166 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1202  ->
    match uu____1202 with
    | (l,n1) ->
        let uu____1207 = FStar_ST.read query_indices in
        (match uu____1207 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1241 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1251  ->
    let uu____1252 = FStar_ST.read query_indices in FStar_List.hd uu____1252
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1268  ->
    let uu____1269 = FStar_ST.read query_indices in
    match uu____1269 with
    | hd1::uu____1281::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1308 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1322 =
       let uu____1324 = FStar_ST.read stack in env :: uu____1324 in
     FStar_ST.write stack uu____1322);
    (let uu___112_1332 = env in
     let uu____1333 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1335 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1332.solver);
       range = (uu___112_1332.range);
       curmodule = (uu___112_1332.curmodule);
       gamma = (uu___112_1332.gamma);
       gamma_cache = uu____1333;
       modules = (uu___112_1332.modules);
       expected_typ = (uu___112_1332.expected_typ);
       sigtab = uu____1335;
       is_pattern = (uu___112_1332.is_pattern);
       instantiate_imp = (uu___112_1332.instantiate_imp);
       effects = (uu___112_1332.effects);
       generalize = (uu___112_1332.generalize);
       letrecs = (uu___112_1332.letrecs);
       top_level = (uu___112_1332.top_level);
       check_uvars = (uu___112_1332.check_uvars);
       use_eq = (uu___112_1332.use_eq);
       is_iface = (uu___112_1332.is_iface);
       admit = (uu___112_1332.admit);
       lax = (uu___112_1332.lax);
       lax_universes = (uu___112_1332.lax_universes);
       type_of = (uu___112_1332.type_of);
       universe_of = (uu___112_1332.universe_of);
       use_bv_sorts = (uu___112_1332.use_bv_sorts);
       qname_and_index = (uu___112_1332.qname_and_index);
       proof_ns = (uu___112_1332.proof_ns)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1339  ->
    let uu____1340 = FStar_ST.read stack in
    match uu____1340 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1352 -> failwith "Impossible: Too many pops"
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
    (let uu____1384 = pop_stack () in ());
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
        let uu____1403 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1415  ->
                  match uu____1415 with
                  | (m,uu____1419) -> FStar_Ident.lid_equals l m)) in
        (match uu____1403 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1424 = env in
               {
                 solver = (uu___113_1424.solver);
                 range = (uu___113_1424.range);
                 curmodule = (uu___113_1424.curmodule);
                 gamma = (uu___113_1424.gamma);
                 gamma_cache = (uu___113_1424.gamma_cache);
                 modules = (uu___113_1424.modules);
                 expected_typ = (uu___113_1424.expected_typ);
                 sigtab = (uu___113_1424.sigtab);
                 is_pattern = (uu___113_1424.is_pattern);
                 instantiate_imp = (uu___113_1424.instantiate_imp);
                 effects = (uu___113_1424.effects);
                 generalize = (uu___113_1424.generalize);
                 letrecs = (uu___113_1424.letrecs);
                 top_level = (uu___113_1424.top_level);
                 check_uvars = (uu___113_1424.check_uvars);
                 use_eq = (uu___113_1424.use_eq);
                 is_iface = (uu___113_1424.is_iface);
                 admit = (uu___113_1424.admit);
                 lax = (uu___113_1424.lax);
                 lax_universes = (uu___113_1424.lax_universes);
                 type_of = (uu___113_1424.type_of);
                 universe_of = (uu___113_1424.universe_of);
                 use_bv_sorts = (uu___113_1424.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_1424.proof_ns)
               }))
         | Some (uu____1427,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1433 = env in
               {
                 solver = (uu___114_1433.solver);
                 range = (uu___114_1433.range);
                 curmodule = (uu___114_1433.curmodule);
                 gamma = (uu___114_1433.gamma);
                 gamma_cache = (uu___114_1433.gamma_cache);
                 modules = (uu___114_1433.modules);
                 expected_typ = (uu___114_1433.expected_typ);
                 sigtab = (uu___114_1433.sigtab);
                 is_pattern = (uu___114_1433.is_pattern);
                 instantiate_imp = (uu___114_1433.instantiate_imp);
                 effects = (uu___114_1433.effects);
                 generalize = (uu___114_1433.generalize);
                 letrecs = (uu___114_1433.letrecs);
                 top_level = (uu___114_1433.top_level);
                 check_uvars = (uu___114_1433.check_uvars);
                 use_eq = (uu___114_1433.use_eq);
                 is_iface = (uu___114_1433.is_iface);
                 admit = (uu___114_1433.admit);
                 lax = (uu___114_1433.lax);
                 lax_universes = (uu___114_1433.lax_universes);
                 type_of = (uu___114_1433.type_of);
                 universe_of = (uu___114_1433.universe_of);
                 use_bv_sorts = (uu___114_1433.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_1433.proof_ns)
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
        (let uu___115_1449 = e in
         {
           solver = (uu___115_1449.solver);
           range = r;
           curmodule = (uu___115_1449.curmodule);
           gamma = (uu___115_1449.gamma);
           gamma_cache = (uu___115_1449.gamma_cache);
           modules = (uu___115_1449.modules);
           expected_typ = (uu___115_1449.expected_typ);
           sigtab = (uu___115_1449.sigtab);
           is_pattern = (uu___115_1449.is_pattern);
           instantiate_imp = (uu___115_1449.instantiate_imp);
           effects = (uu___115_1449.effects);
           generalize = (uu___115_1449.generalize);
           letrecs = (uu___115_1449.letrecs);
           top_level = (uu___115_1449.top_level);
           check_uvars = (uu___115_1449.check_uvars);
           use_eq = (uu___115_1449.use_eq);
           is_iface = (uu___115_1449.is_iface);
           admit = (uu___115_1449.admit);
           lax = (uu___115_1449.lax);
           lax_universes = (uu___115_1449.lax_universes);
           type_of = (uu___115_1449.type_of);
           universe_of = (uu___115_1449.universe_of);
           use_bv_sorts = (uu___115_1449.use_bv_sorts);
           qname_and_index = (uu___115_1449.qname_and_index);
           proof_ns = (uu___115_1449.proof_ns)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1466 = env in
      {
        solver = (uu___116_1466.solver);
        range = (uu___116_1466.range);
        curmodule = lid;
        gamma = (uu___116_1466.gamma);
        gamma_cache = (uu___116_1466.gamma_cache);
        modules = (uu___116_1466.modules);
        expected_typ = (uu___116_1466.expected_typ);
        sigtab = (uu___116_1466.sigtab);
        is_pattern = (uu___116_1466.is_pattern);
        instantiate_imp = (uu___116_1466.instantiate_imp);
        effects = (uu___116_1466.effects);
        generalize = (uu___116_1466.generalize);
        letrecs = (uu___116_1466.letrecs);
        top_level = (uu___116_1466.top_level);
        check_uvars = (uu___116_1466.check_uvars);
        use_eq = (uu___116_1466.use_eq);
        is_iface = (uu___116_1466.is_iface);
        admit = (uu___116_1466.admit);
        lax = (uu___116_1466.lax);
        lax_universes = (uu___116_1466.lax_universes);
        type_of = (uu___116_1466.type_of);
        universe_of = (uu___116_1466.universe_of);
        use_bv_sorts = (uu___116_1466.use_bv_sorts);
        qname_and_index = (uu___116_1466.qname_and_index);
        proof_ns = (uu___116_1466.proof_ns)
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
    let uu____1488 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1488
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1491  ->
    let uu____1492 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1492
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1514) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1530 = FStar_Syntax_Subst.subst vs t in (us, uu____1530)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1535  ->
    match uu___100_1535 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1549  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1559 = inst_tscheme t in
      match uu____1559 with
      | (us,t1) ->
          let uu____1566 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1566)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1578  ->
          match uu____1578 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1592 =
                         let uu____1593 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1596 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1599 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1600 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1593 uu____1596 uu____1599 uu____1600 in
                       failwith uu____1592)
                    else ();
                    (let uu____1602 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1602))
               | uu____1606 ->
                   let uu____1607 =
                     let uu____1608 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1608 in
                   failwith uu____1607)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1612 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1616 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1620 -> false
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
             | ([],uu____1646) -> Maybe
             | (uu____1650,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1662 -> No in
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
          let uu____1722 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1722 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1743  ->
                   match uu___101_1743 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1766 =
                           let uu____1776 =
                             let uu____1784 = inst_tscheme t in
                             FStar_Util.Inl uu____1784 in
                           (uu____1776, (FStar_Ident.range_of_lid l)) in
                         Some uu____1766
                       else None
                   | Binding_sig
                       (uu____1818,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1820);
                                     FStar_Syntax_Syntax.sigrng = uu____1821;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1822;
                                     FStar_Syntax_Syntax.sigmeta = uu____1823;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1832 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1832
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1859 ->
                             Some t
                         | uu____1863 -> cache t in
                       let uu____1864 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1864 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1904 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1904 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1948 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1990 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1990
         then
           let uu____2001 = find_in_sigtab env lid in
           match uu____2001 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2067) ->
          add_sigelts env ses
      | uu____2072 ->
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
            | uu____2081 -> ()))
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
        (fun uu___102_2099  ->
           match uu___102_2099 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2112 -> None)
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
          ((uu____2133,lb::[]),uu____2135,uu____2136) ->
          let uu____2145 =
            let uu____2150 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2156 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2150, uu____2156) in
          Some uu____2145
      | FStar_Syntax_Syntax.Sig_let ((uu____2163,lbs),uu____2165,uu____2166)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2186 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2193 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2193
                   then
                     let uu____2199 =
                       let uu____2204 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2210 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2204, uu____2210) in
                     Some uu____2199
                   else None)
      | uu____2222 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2241 =
          let uu____2246 =
            let uu____2249 =
              let uu____2250 =
                let uu____2253 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2253 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2250) in
            inst_tscheme uu____2249 in
          (uu____2246, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2241
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2267,uu____2268) ->
        let uu____2271 =
          let uu____2276 =
            let uu____2279 =
              let uu____2280 =
                let uu____2283 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2283 in
              (us, uu____2280) in
            inst_tscheme uu____2279 in
          (uu____2276, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2271
    | uu____2294 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2329 =
        match uu____2329 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2379,uvs,t,uu____2382,uu____2383,uu____2384);
                    FStar_Syntax_Syntax.sigrng = uu____2385;
                    FStar_Syntax_Syntax.sigquals = uu____2386;
                    FStar_Syntax_Syntax.sigmeta = uu____2387;_},None
                  )
                 ->
                 let uu____2397 =
                   let uu____2402 = inst_tscheme (uvs, t) in
                   (uu____2402, rng) in
                 Some uu____2397
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2414;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2416;_},None
                  )
                 ->
                 let uu____2424 =
                   let uu____2425 = in_cur_mod env l in uu____2425 = Yes in
                 if uu____2424
                 then
                   let uu____2431 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2431
                    then
                      let uu____2438 =
                        let uu____2443 = inst_tscheme (uvs, t) in
                        (uu____2443, rng) in
                      Some uu____2438
                    else None)
                 else
                   (let uu____2458 =
                      let uu____2463 = inst_tscheme (uvs, t) in
                      (uu____2463, rng) in
                    Some uu____2458)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2476,uu____2477);
                    FStar_Syntax_Syntax.sigrng = uu____2478;
                    FStar_Syntax_Syntax.sigquals = uu____2479;
                    FStar_Syntax_Syntax.sigmeta = uu____2480;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2499 =
                        let uu____2504 = inst_tscheme (uvs, k) in
                        (uu____2504, rng) in
                      Some uu____2499
                  | uu____2513 ->
                      let uu____2514 =
                        let uu____2519 =
                          let uu____2522 =
                            let uu____2523 =
                              let uu____2526 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2526 in
                            (uvs, uu____2523) in
                          inst_tscheme uu____2522 in
                        (uu____2519, rng) in
                      Some uu____2514)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2541,uu____2542);
                    FStar_Syntax_Syntax.sigrng = uu____2543;
                    FStar_Syntax_Syntax.sigquals = uu____2544;
                    FStar_Syntax_Syntax.sigmeta = uu____2545;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2565 =
                        let uu____2570 = inst_tscheme_with (uvs, k) us in
                        (uu____2570, rng) in
                      Some uu____2565
                  | uu____2579 ->
                      let uu____2580 =
                        let uu____2585 =
                          let uu____2588 =
                            let uu____2589 =
                              let uu____2592 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2592 in
                            (uvs, uu____2589) in
                          inst_tscheme_with uu____2588 us in
                        (uu____2585, rng) in
                      Some uu____2580)
             | FStar_Util.Inr se ->
                 let uu____2612 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2623;
                        FStar_Syntax_Syntax.sigrng = uu____2624;
                        FStar_Syntax_Syntax.sigquals = uu____2625;
                        FStar_Syntax_Syntax.sigmeta = uu____2626;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2635 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2612
                   (FStar_Util.map_option
                      (fun uu____2658  ->
                         match uu____2658 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2675 =
        let uu____2681 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2681 mapper in
      match uu____2675 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2733 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2733.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2733.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2733.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2754 = lookup_qname env l in
      match uu____2754 with | None  -> false | Some uu____2774 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2802 = try_lookup_bv env bv in
      match uu____2802 with
      | None  ->
          let uu____2810 =
            let uu____2811 =
              let uu____2814 = variable_not_found bv in (uu____2814, bvr) in
            FStar_Errors.Error uu____2811 in
          raise uu____2810
      | Some (t,r) ->
          let uu____2821 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2822 = FStar_Range.set_use_range r bvr in
          (uu____2821, uu____2822)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2834 = try_lookup_lid_aux env l in
      match uu____2834 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2876 =
            let uu____2881 =
              let uu____2884 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2884) in
            (uu____2881, r1) in
          Some uu____2876
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2901 = try_lookup_lid env l in
      match uu____2901 with
      | None  ->
          let uu____2915 =
            let uu____2916 =
              let uu____2919 = name_not_found l in
              (uu____2919, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2916 in
          raise uu____2915
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2940  ->
              match uu___103_2940 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2942 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2953 = lookup_qname env lid in
      match uu____2953 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2968,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2971;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2973;_},None
            ),uu____2974)
          ->
          let uu____2998 =
            let uu____3004 =
              let uu____3007 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____3007) in
            (uu____3004, q) in
          Some uu____2998
      | uu____3016 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3038 = lookup_qname env lid in
      match uu____3038 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3051,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3054;
              FStar_Syntax_Syntax.sigquals = uu____3055;
              FStar_Syntax_Syntax.sigmeta = uu____3056;_},None
            ),uu____3057)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3081 ->
          let uu____3092 =
            let uu____3093 =
              let uu____3096 = name_not_found lid in
              (uu____3096, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3093 in
          raise uu____3092
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3107 = lookup_qname env lid in
      match uu____3107 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3120,uvs,t,uu____3123,uu____3124,uu____3125);
              FStar_Syntax_Syntax.sigrng = uu____3126;
              FStar_Syntax_Syntax.sigquals = uu____3127;
              FStar_Syntax_Syntax.sigmeta = uu____3128;_},None
            ),uu____3129)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3155 ->
          let uu____3166 =
            let uu____3167 =
              let uu____3170 = name_not_found lid in
              (uu____3170, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3167 in
          raise uu____3166
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3182 = lookup_qname env lid in
      match uu____3182 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3196,uu____3197,uu____3198,uu____3199,uu____3200,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3202;
              FStar_Syntax_Syntax.sigquals = uu____3203;
              FStar_Syntax_Syntax.sigmeta = uu____3204;_},uu____3205),uu____3206)
          -> (true, dcs)
      | uu____3236 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3254 = lookup_qname env lid in
      match uu____3254 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3265,uu____3266,uu____3267,l,uu____3269,uu____3270);
              FStar_Syntax_Syntax.sigrng = uu____3271;
              FStar_Syntax_Syntax.sigquals = uu____3272;
              FStar_Syntax_Syntax.sigmeta = uu____3273;_},uu____3274),uu____3275)
          -> l
      | uu____3302 ->
          let uu____3313 =
            let uu____3314 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3314 in
          failwith uu____3313
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
        let uu____3338 = lookup_qname env lid in
        match uu____3338 with
        | Some (FStar_Util.Inr (se,None ),uu____3353) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3379,lbs),uu____3381,uu____3382) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3399 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3399
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3420 -> None)
        | uu____3423 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3444 = lookup_qname env ftv in
      match uu____3444 with
      | Some (FStar_Util.Inr (se,None ),uu____3457) ->
          let uu____3480 = effect_signature se in
          (match uu____3480 with
           | None  -> None
           | Some ((uu____3491,t),r) ->
               let uu____3500 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3500)
      | uu____3501 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3518 = try_lookup_effect_lid env ftv in
      match uu____3518 with
      | None  ->
          let uu____3520 =
            let uu____3521 =
              let uu____3524 = name_not_found ftv in
              (uu____3524, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3521 in
          raise uu____3520
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
        let uu____3538 = lookup_qname env lid0 in
        match uu____3538 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3556);
                FStar_Syntax_Syntax.sigrng = uu____3557;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3559;_},None
              ),uu____3560)
            ->
            let lid1 =
              let uu____3587 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3587 in
            let uu____3588 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3590  ->
                      match uu___104_3590 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3591 -> false)) in
            if uu____3588
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
                     (let uu____3607 =
                        let uu____3608 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3609 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3608 uu____3609 in
                      failwith uu____3607) in
               match (binders, univs1) with
               | ([],uu____3615) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3624,uu____3625::uu____3626::uu____3627) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3630 =
                     let uu____3631 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3632 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3631 uu____3632 in
                   failwith uu____3630
               | uu____3638 ->
                   let uu____3641 =
                     let uu____3644 =
                       let uu____3645 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3645) in
                     inst_tscheme_with uu____3644 insts in
                   (match uu____3641 with
                    | (uu____3653,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3656 =
                          let uu____3657 = FStar_Syntax_Subst.compress t1 in
                          uu____3657.FStar_Syntax_Syntax.n in
                        (match uu____3656 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3687 -> failwith "Impossible")))
        | uu____3691 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3717 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3717 with
        | None  -> None
        | Some (uu____3724,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3729 = find1 l2 in
            (match uu____3729 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3734 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3734 with
        | Some l1 -> l1
        | None  ->
            let uu____3737 = find1 l in
            (match uu____3737 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3749 = lookup_qname env l1 in
      match uu____3749 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3761;
              FStar_Syntax_Syntax.sigrng = uu____3762;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3764;_},uu____3765),uu____3766)
          -> q
      | uu____3791 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3814 =
          let uu____3815 =
            let uu____3816 = FStar_Util.string_of_int i in
            let uu____3817 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3816 uu____3817 in
          failwith uu____3815 in
        let uu____3818 = lookup_datacon env lid in
        match uu____3818 with
        | (uu____3821,t) ->
            let uu____3823 =
              let uu____3824 = FStar_Syntax_Subst.compress t in
              uu____3824.FStar_Syntax_Syntax.n in
            (match uu____3823 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3828) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3849 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3849 FStar_Pervasives.fst)
             | uu____3854 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3861 = lookup_qname env l in
      match uu____3861 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3872,uu____3873,uu____3874);
              FStar_Syntax_Syntax.sigrng = uu____3875;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3877;_},uu____3878),uu____3879)
          ->
          FStar_Util.for_some
            (fun uu___105_3904  ->
               match uu___105_3904 with
               | FStar_Syntax_Syntax.Projector uu____3905 -> true
               | uu____3908 -> false) quals
      | uu____3909 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3926 = lookup_qname env lid in
      match uu____3926 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3937,uu____3938,uu____3939,uu____3940,uu____3941,uu____3942);
              FStar_Syntax_Syntax.sigrng = uu____3943;
              FStar_Syntax_Syntax.sigquals = uu____3944;
              FStar_Syntax_Syntax.sigmeta = uu____3945;_},uu____3946),uu____3947)
          -> true
      | uu____3974 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3991 = lookup_qname env lid in
      match uu____3991 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4002,uu____4003,uu____4004,uu____4005,uu____4006,uu____4007);
              FStar_Syntax_Syntax.sigrng = uu____4008;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4010;_},uu____4011),uu____4012)
          ->
          FStar_Util.for_some
            (fun uu___106_4041  ->
               match uu___106_4041 with
               | FStar_Syntax_Syntax.RecordType uu____4042 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4047 -> true
               | uu____4052 -> false) quals
      | uu____4053 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4070 = lookup_qname env lid in
      match uu____4070 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4081,uu____4082,uu____4083);
              FStar_Syntax_Syntax.sigrng = uu____4084;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4086;_},uu____4087),uu____4088)
          ->
          FStar_Util.for_some
            (fun uu___107_4117  ->
               match uu___107_4117 with
               | FStar_Syntax_Syntax.Action uu____4118 -> true
               | uu____4119 -> false) quals
      | uu____4120 -> false
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
      let uu____4139 =
        let uu____4140 = FStar_Syntax_Util.un_uinst head1 in
        uu____4140.FStar_Syntax_Syntax.n in
      match uu____4139 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4144 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4182 -> Some false
        | FStar_Util.Inr (se,uu____4191) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4200 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4204 -> Some true
             | uu____4213 -> Some false) in
      let uu____4214 =
        let uu____4216 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4216 mapper in
      match uu____4214 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4243 = lookup_qname env lid in
      match uu____4243 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4254,uu____4255,tps,uu____4257,uu____4258,uu____4259);
              FStar_Syntax_Syntax.sigrng = uu____4260;
              FStar_Syntax_Syntax.sigquals = uu____4261;
              FStar_Syntax_Syntax.sigmeta = uu____4262;_},uu____4263),uu____4264)
          -> FStar_List.length tps
      | uu____4296 ->
          let uu____4307 =
            let uu____4308 =
              let uu____4311 = name_not_found lid in
              (uu____4311, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4308 in
          raise uu____4307
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
           (fun uu____4333  ->
              match uu____4333 with
              | (d,uu____4338) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4347 = effect_decl_opt env l in
      match uu____4347 with
      | None  ->
          let uu____4355 =
            let uu____4356 =
              let uu____4359 = name_not_found l in
              (uu____4359, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4356 in
          raise uu____4355
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
            (let uu____4402 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4426  ->
                       match uu____4426 with
                       | (m1,m2,uu____4434,uu____4435,uu____4436) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4402 with
             | None  ->
                 let uu____4445 =
                   let uu____4446 =
                     let uu____4449 =
                       let uu____4450 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4451 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4450
                         uu____4451 in
                     (uu____4449, (env.range)) in
                   FStar_Errors.Error uu____4446 in
                 raise uu____4445
             | Some (uu____4455,uu____4456,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4503 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4515  ->
            match uu____4515 with
            | (d,uu____4519) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4503 with
  | None  ->
      let uu____4526 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4526
  | Some (md,_q) ->
      let uu____4535 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4535 with
       | (uu____4542,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4550)::(wp,uu____4552)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4574 -> failwith "Impossible"))
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
                 let uu____4610 = get_range env in
                 let uu____4611 =
                   let uu____4614 =
                     let uu____4615 =
                       let uu____4625 =
                         let uu____4627 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4627] in
                       (null_wp, uu____4625) in
                     FStar_Syntax_Syntax.Tm_app uu____4615 in
                   FStar_Syntax_Syntax.mk uu____4614 in
                 uu____4611 None uu____4610 in
               let uu____4637 =
                 let uu____4638 =
                   let uu____4644 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4644] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4638;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4637)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4653 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4653.order);
              joins = (uu___118_4653.joins)
            } in
          let uu___119_4658 = env in
          {
            solver = (uu___119_4658.solver);
            range = (uu___119_4658.range);
            curmodule = (uu___119_4658.curmodule);
            gamma = (uu___119_4658.gamma);
            gamma_cache = (uu___119_4658.gamma_cache);
            modules = (uu___119_4658.modules);
            expected_typ = (uu___119_4658.expected_typ);
            sigtab = (uu___119_4658.sigtab);
            is_pattern = (uu___119_4658.is_pattern);
            instantiate_imp = (uu___119_4658.instantiate_imp);
            effects;
            generalize = (uu___119_4658.generalize);
            letrecs = (uu___119_4658.letrecs);
            top_level = (uu___119_4658.top_level);
            check_uvars = (uu___119_4658.check_uvars);
            use_eq = (uu___119_4658.use_eq);
            is_iface = (uu___119_4658.is_iface);
            admit = (uu___119_4658.admit);
            lax = (uu___119_4658.lax);
            lax_universes = (uu___119_4658.lax_universes);
            type_of = (uu___119_4658.type_of);
            universe_of = (uu___119_4658.universe_of);
            use_bv_sorts = (uu___119_4658.use_bv_sorts);
            qname_and_index = (uu___119_4658.qname_and_index);
            proof_ns = (uu___119_4658.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4675 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4675 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4754 = (e1.mlift).mlift_wp t wp in
                              let uu____4755 = l1 t wp e in
                              l2 t uu____4754 uu____4755))
                | uu____4756 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4791 = inst_tscheme lift_t in
            match uu____4791 with
            | (uu____4796,lift_t1) ->
                let uu____4798 =
                  let uu____4801 =
                    let uu____4802 =
                      let uu____4812 =
                        let uu____4814 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4815 =
                          let uu____4817 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4817] in
                        uu____4814 :: uu____4815 in
                      (lift_t1, uu____4812) in
                    FStar_Syntax_Syntax.Tm_app uu____4802 in
                  FStar_Syntax_Syntax.mk uu____4801 in
                uu____4798 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4862 = inst_tscheme lift_t in
            match uu____4862 with
            | (uu____4867,lift_t1) ->
                let uu____4869 =
                  let uu____4872 =
                    let uu____4873 =
                      let uu____4883 =
                        let uu____4885 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4886 =
                          let uu____4888 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4889 =
                            let uu____4891 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4891] in
                          uu____4888 :: uu____4889 in
                        uu____4885 :: uu____4886 in
                      (lift_t1, uu____4883) in
                    FStar_Syntax_Syntax.Tm_app uu____4873 in
                  FStar_Syntax_Syntax.mk uu____4872 in
                uu____4869 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4932 =
                let uu____4933 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4933
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4932 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4937 =
              let uu____4938 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4938 in
            let uu____4939 =
              let uu____4940 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4955 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4955) in
              FStar_Util.dflt "none" uu____4940 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4937
              uu____4939 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4968  ->
                    match uu____4968 with
                    | (e,uu____4973) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4986 =
            match uu____4986 with
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
              let uu____5011 =
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
              FStar_List.append order1 uu____5011 in
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
                   let uu____5055 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5056 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5056
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5055
                   then
                     let uu____5059 =
                       let uu____5060 =
                         let uu____5063 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5064 = get_range env in
                         (uu____5063, uu____5064) in
                       FStar_Errors.Error uu____5060 in
                     raise uu____5059
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
                                            let uu____5127 =
                                              let uu____5132 =
                                                find_edge order2 (i, k) in
                                              let uu____5134 =
                                                find_edge order2 (j, k) in
                                              (uu____5132, uu____5134) in
                                            match uu____5127 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5157,uu____5158)
                                                     ->
                                                     let uu____5162 =
                                                       let uu____5165 =
                                                         let uu____5166 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5166 in
                                                       let uu____5168 =
                                                         let uu____5169 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5169 in
                                                       (uu____5165,
                                                         uu____5168) in
                                                     (match uu____5162 with
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
                                            | uu____5188 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5227 = env.effects in
              { decls = (uu___120_5227.decls); order = order2; joins } in
            let uu___121_5228 = env in
            {
              solver = (uu___121_5228.solver);
              range = (uu___121_5228.range);
              curmodule = (uu___121_5228.curmodule);
              gamma = (uu___121_5228.gamma);
              gamma_cache = (uu___121_5228.gamma_cache);
              modules = (uu___121_5228.modules);
              expected_typ = (uu___121_5228.expected_typ);
              sigtab = (uu___121_5228.sigtab);
              is_pattern = (uu___121_5228.is_pattern);
              instantiate_imp = (uu___121_5228.instantiate_imp);
              effects;
              generalize = (uu___121_5228.generalize);
              letrecs = (uu___121_5228.letrecs);
              top_level = (uu___121_5228.top_level);
              check_uvars = (uu___121_5228.check_uvars);
              use_eq = (uu___121_5228.use_eq);
              is_iface = (uu___121_5228.is_iface);
              admit = (uu___121_5228.admit);
              lax = (uu___121_5228.lax);
              lax_universes = (uu___121_5228.lax_universes);
              type_of = (uu___121_5228.type_of);
              universe_of = (uu___121_5228.universe_of);
              use_bv_sorts = (uu___121_5228.use_bv_sorts);
              qname_and_index = (uu___121_5228.qname_and_index);
              proof_ns = (uu___121_5228.proof_ns)
            }))
      | uu____5229 -> env
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
        | uu____5251 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5259 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5259 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5269 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5269 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5286 =
                     let uu____5287 =
                       let uu____5290 =
                         let uu____5291 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5297 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5305 =
                           let uu____5306 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5306 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5291 uu____5297 uu____5305 in
                       (uu____5290, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5287 in
                   raise uu____5286)
                else ();
                (let inst1 =
                   let uu____5310 =
                     let uu____5316 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5316 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5323  ->
                        fun uu____5324  ->
                          match (uu____5323, uu____5324) with
                          | ((x,uu____5338),(t,uu____5340)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5310 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5355 =
                     let uu___122_5356 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5356.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5356.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5356.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5356.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5355
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5386 =
    let uu____5391 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5391 in
  match uu____5386 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5407 =
        only_reifiable &&
          (let uu____5408 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5408) in
      if uu____5407
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5421 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5423 =
               let uu____5432 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5432) in
             (match uu____5423 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5466 =
                    let uu____5469 = get_range env in
                    let uu____5470 =
                      let uu____5473 =
                        let uu____5474 =
                          let uu____5484 =
                            let uu____5486 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5486; wp] in
                          (repr, uu____5484) in
                        FStar_Syntax_Syntax.Tm_app uu____5474 in
                      FStar_Syntax_Syntax.mk uu____5473 in
                    uu____5470 None uu____5469 in
                  Some uu____5466))
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
          let uu____5530 =
            let uu____5531 =
              let uu____5534 =
                let uu____5535 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5535 in
              let uu____5536 = get_range env in (uu____5534, uu____5536) in
            FStar_Errors.Error uu____5531 in
          raise uu____5530 in
        let uu____5537 = effect_repr_aux true env c u_c in
        match uu____5537 with
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
        | FStar_Util.Inr (eff_name,uu____5569) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5582 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5589 =
        let uu____5590 = FStar_Syntax_Subst.compress t in
        uu____5590.FStar_Syntax_Syntax.n in
      match uu____5589 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5593,c) ->
          is_reifiable_comp env c
      | uu____5605 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5623)::uu____5624 -> x :: rest
        | (Binding_sig_inst uu____5629)::uu____5630 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5639 = push1 x rest1 in local :: uu____5639 in
      let uu___123_5641 = env in
      let uu____5642 = push1 s env.gamma in
      {
        solver = (uu___123_5641.solver);
        range = (uu___123_5641.range);
        curmodule = (uu___123_5641.curmodule);
        gamma = uu____5642;
        gamma_cache = (uu___123_5641.gamma_cache);
        modules = (uu___123_5641.modules);
        expected_typ = (uu___123_5641.expected_typ);
        sigtab = (uu___123_5641.sigtab);
        is_pattern = (uu___123_5641.is_pattern);
        instantiate_imp = (uu___123_5641.instantiate_imp);
        effects = (uu___123_5641.effects);
        generalize = (uu___123_5641.generalize);
        letrecs = (uu___123_5641.letrecs);
        top_level = (uu___123_5641.top_level);
        check_uvars = (uu___123_5641.check_uvars);
        use_eq = (uu___123_5641.use_eq);
        is_iface = (uu___123_5641.is_iface);
        admit = (uu___123_5641.admit);
        lax = (uu___123_5641.lax);
        lax_universes = (uu___123_5641.lax_universes);
        type_of = (uu___123_5641.type_of);
        universe_of = (uu___123_5641.universe_of);
        use_bv_sorts = (uu___123_5641.use_bv_sorts);
        qname_and_index = (uu___123_5641.qname_and_index);
        proof_ns = (uu___123_5641.proof_ns)
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
      let uu___124_5669 = env in
      {
        solver = (uu___124_5669.solver);
        range = (uu___124_5669.range);
        curmodule = (uu___124_5669.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5669.gamma_cache);
        modules = (uu___124_5669.modules);
        expected_typ = (uu___124_5669.expected_typ);
        sigtab = (uu___124_5669.sigtab);
        is_pattern = (uu___124_5669.is_pattern);
        instantiate_imp = (uu___124_5669.instantiate_imp);
        effects = (uu___124_5669.effects);
        generalize = (uu___124_5669.generalize);
        letrecs = (uu___124_5669.letrecs);
        top_level = (uu___124_5669.top_level);
        check_uvars = (uu___124_5669.check_uvars);
        use_eq = (uu___124_5669.use_eq);
        is_iface = (uu___124_5669.is_iface);
        admit = (uu___124_5669.admit);
        lax = (uu___124_5669.lax);
        lax_universes = (uu___124_5669.lax_universes);
        type_of = (uu___124_5669.type_of);
        universe_of = (uu___124_5669.universe_of);
        use_bv_sorts = (uu___124_5669.use_bv_sorts);
        qname_and_index = (uu___124_5669.qname_and_index);
        proof_ns = (uu___124_5669.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5690 = env in
             {
               solver = (uu___125_5690.solver);
               range = (uu___125_5690.range);
               curmodule = (uu___125_5690.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5690.gamma_cache);
               modules = (uu___125_5690.modules);
               expected_typ = (uu___125_5690.expected_typ);
               sigtab = (uu___125_5690.sigtab);
               is_pattern = (uu___125_5690.is_pattern);
               instantiate_imp = (uu___125_5690.instantiate_imp);
               effects = (uu___125_5690.effects);
               generalize = (uu___125_5690.generalize);
               letrecs = (uu___125_5690.letrecs);
               top_level = (uu___125_5690.top_level);
               check_uvars = (uu___125_5690.check_uvars);
               use_eq = (uu___125_5690.use_eq);
               is_iface = (uu___125_5690.is_iface);
               admit = (uu___125_5690.admit);
               lax = (uu___125_5690.lax);
               lax_universes = (uu___125_5690.lax_universes);
               type_of = (uu___125_5690.type_of);
               universe_of = (uu___125_5690.universe_of);
               use_bv_sorts = (uu___125_5690.use_bv_sorts);
               qname_and_index = (uu___125_5690.qname_and_index);
               proof_ns = (uu___125_5690.proof_ns)
             }))
    | uu____5691 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5704  ->
             match uu____5704 with | (x,uu____5708) -> push_bv env1 x) env bs
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
            let uu___126_5728 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5728.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5728.FStar_Syntax_Syntax.index);
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
      (let uu___127_5758 = env in
       {
         solver = (uu___127_5758.solver);
         range = (uu___127_5758.range);
         curmodule = (uu___127_5758.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5758.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5758.sigtab);
         is_pattern = (uu___127_5758.is_pattern);
         instantiate_imp = (uu___127_5758.instantiate_imp);
         effects = (uu___127_5758.effects);
         generalize = (uu___127_5758.generalize);
         letrecs = (uu___127_5758.letrecs);
         top_level = (uu___127_5758.top_level);
         check_uvars = (uu___127_5758.check_uvars);
         use_eq = (uu___127_5758.use_eq);
         is_iface = (uu___127_5758.is_iface);
         admit = (uu___127_5758.admit);
         lax = (uu___127_5758.lax);
         lax_universes = (uu___127_5758.lax_universes);
         type_of = (uu___127_5758.type_of);
         universe_of = (uu___127_5758.universe_of);
         use_bv_sorts = (uu___127_5758.use_bv_sorts);
         qname_and_index = (uu___127_5758.qname_and_index);
         proof_ns = (uu___127_5758.proof_ns)
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
        let uu____5782 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5782 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5798 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5798)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5808 = env in
      {
        solver = (uu___128_5808.solver);
        range = (uu___128_5808.range);
        curmodule = (uu___128_5808.curmodule);
        gamma = (uu___128_5808.gamma);
        gamma_cache = (uu___128_5808.gamma_cache);
        modules = (uu___128_5808.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5808.sigtab);
        is_pattern = (uu___128_5808.is_pattern);
        instantiate_imp = (uu___128_5808.instantiate_imp);
        effects = (uu___128_5808.effects);
        generalize = (uu___128_5808.generalize);
        letrecs = (uu___128_5808.letrecs);
        top_level = (uu___128_5808.top_level);
        check_uvars = (uu___128_5808.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5808.is_iface);
        admit = (uu___128_5808.admit);
        lax = (uu___128_5808.lax);
        lax_universes = (uu___128_5808.lax_universes);
        type_of = (uu___128_5808.type_of);
        universe_of = (uu___128_5808.universe_of);
        use_bv_sorts = (uu___128_5808.use_bv_sorts);
        qname_and_index = (uu___128_5808.qname_and_index);
        proof_ns = (uu___128_5808.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5824 = expected_typ env_ in
    ((let uu___129_5827 = env_ in
      {
        solver = (uu___129_5827.solver);
        range = (uu___129_5827.range);
        curmodule = (uu___129_5827.curmodule);
        gamma = (uu___129_5827.gamma);
        gamma_cache = (uu___129_5827.gamma_cache);
        modules = (uu___129_5827.modules);
        expected_typ = None;
        sigtab = (uu___129_5827.sigtab);
        is_pattern = (uu___129_5827.is_pattern);
        instantiate_imp = (uu___129_5827.instantiate_imp);
        effects = (uu___129_5827.effects);
        generalize = (uu___129_5827.generalize);
        letrecs = (uu___129_5827.letrecs);
        top_level = (uu___129_5827.top_level);
        check_uvars = (uu___129_5827.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5827.is_iface);
        admit = (uu___129_5827.admit);
        lax = (uu___129_5827.lax);
        lax_universes = (uu___129_5827.lax_universes);
        type_of = (uu___129_5827.type_of);
        universe_of = (uu___129_5827.universe_of);
        use_bv_sorts = (uu___129_5827.use_bv_sorts);
        qname_and_index = (uu___129_5827.qname_and_index);
        proof_ns = (uu___129_5827.proof_ns)
      }), uu____5824)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5838 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5842  ->
                    match uu___108_5842 with
                    | Binding_sig (uu____5844,se) -> [se]
                    | uu____5848 -> [])) in
          FStar_All.pipe_right uu____5838 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5853 = env in
       {
         solver = (uu___130_5853.solver);
         range = (uu___130_5853.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5853.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5853.expected_typ);
         sigtab = (uu___130_5853.sigtab);
         is_pattern = (uu___130_5853.is_pattern);
         instantiate_imp = (uu___130_5853.instantiate_imp);
         effects = (uu___130_5853.effects);
         generalize = (uu___130_5853.generalize);
         letrecs = (uu___130_5853.letrecs);
         top_level = (uu___130_5853.top_level);
         check_uvars = (uu___130_5853.check_uvars);
         use_eq = (uu___130_5853.use_eq);
         is_iface = (uu___130_5853.is_iface);
         admit = (uu___130_5853.admit);
         lax = (uu___130_5853.lax);
         lax_universes = (uu___130_5853.lax_universes);
         type_of = (uu___130_5853.type_of);
         universe_of = (uu___130_5853.universe_of);
         use_bv_sorts = (uu___130_5853.use_bv_sorts);
         qname_and_index = (uu___130_5853.qname_and_index);
         proof_ns = (uu___130_5853.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5903)::tl1 -> aux out tl1
      | (Binding_lid (uu____5906,(uu____5907,t)))::tl1 ->
          let uu____5916 =
            let uu____5920 = FStar_Syntax_Free.uvars t in ext out uu____5920 in
          aux uu____5916 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5924;
            FStar_Syntax_Syntax.index = uu____5925;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5931 =
            let uu____5935 = FStar_Syntax_Free.uvars t in ext out uu____5935 in
          aux uu____5931 tl1
      | (Binding_sig uu____5939)::uu____5940 -> out
      | (Binding_sig_inst uu____5945)::uu____5946 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5983)::tl1 -> aux out tl1
      | (Binding_univ uu____5990)::tl1 -> aux out tl1
      | (Binding_lid (uu____5993,(uu____5994,t)))::tl1 ->
          let uu____6003 =
            let uu____6005 = FStar_Syntax_Free.univs t in ext out uu____6005 in
          aux uu____6003 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6007;
            FStar_Syntax_Syntax.index = uu____6008;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6014 =
            let uu____6016 = FStar_Syntax_Free.univs t in ext out uu____6016 in
          aux uu____6014 tl1
      | (Binding_sig uu____6018)::uu____6019 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6056)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6066 = FStar_Util.set_add uname out in aux uu____6066 tl1
      | (Binding_lid (uu____6068,(uu____6069,t)))::tl1 ->
          let uu____6078 =
            let uu____6080 = FStar_Syntax_Free.univnames t in
            ext out uu____6080 in
          aux uu____6078 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6082;
            FStar_Syntax_Syntax.index = uu____6083;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6089 =
            let uu____6091 = FStar_Syntax_Free.univnames t in
            ext out uu____6091 in
          aux uu____6089 tl1
      | (Binding_sig uu____6093)::uu____6094 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6110  ->
            match uu___109_6110 with
            | Binding_var x -> [x]
            | Binding_lid uu____6113 -> []
            | Binding_sig uu____6116 -> []
            | Binding_univ uu____6120 -> []
            | Binding_sig_inst uu____6121 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6131 =
      let uu____6133 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6133
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6131 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6149 =
      let uu____6150 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6154  ->
                match uu___110_6154 with
                | Binding_var x ->
                    let uu____6156 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6156
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6159) ->
                    let uu____6160 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6160
                | Binding_sig (ls,uu____6162) ->
                    let uu____6165 =
                      let uu____6166 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6166
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6165
                | Binding_sig_inst (ls,uu____6172,uu____6173) ->
                    let uu____6176 =
                      let uu____6177 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6177
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6176)) in
      FStar_All.pipe_right uu____6150 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6149 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6189 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6189
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6206  ->
                 fun uu____6207  ->
                   match (uu____6206, uu____6207) with
                   | ((b1,uu____6217),(b2,uu____6219)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6262  ->
             match uu___111_6262 with
             | Binding_sig (lids,uu____6266) -> FStar_List.append lids keys
             | uu____6269 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6271  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6296) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6308,uu____6309) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6333 = list_prefix p path1 in
            if uu____6333 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6343 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6343
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6363 = e in
            {
              solver = (uu___131_6363.solver);
              range = (uu___131_6363.range);
              curmodule = (uu___131_6363.curmodule);
              gamma = (uu___131_6363.gamma);
              gamma_cache = (uu___131_6363.gamma_cache);
              modules = (uu___131_6363.modules);
              expected_typ = (uu___131_6363.expected_typ);
              sigtab = (uu___131_6363.sigtab);
              is_pattern = (uu___131_6363.is_pattern);
              instantiate_imp = (uu___131_6363.instantiate_imp);
              effects = (uu___131_6363.effects);
              generalize = (uu___131_6363.generalize);
              letrecs = (uu___131_6363.letrecs);
              top_level = (uu___131_6363.top_level);
              check_uvars = (uu___131_6363.check_uvars);
              use_eq = (uu___131_6363.use_eq);
              is_iface = (uu___131_6363.is_iface);
              admit = (uu___131_6363.admit);
              lax = (uu___131_6363.lax);
              lax_universes = (uu___131_6363.lax_universes);
              type_of = (uu___131_6363.type_of);
              universe_of = (uu___131_6363.universe_of);
              use_bv_sorts = (uu___131_6363.use_bv_sorts);
              qname_and_index = (uu___131_6363.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6382 = e in
    {
      solver = (uu___132_6382.solver);
      range = (uu___132_6382.range);
      curmodule = (uu___132_6382.curmodule);
      gamma = (uu___132_6382.gamma);
      gamma_cache = (uu___132_6382.gamma_cache);
      modules = (uu___132_6382.modules);
      expected_typ = (uu___132_6382.expected_typ);
      sigtab = (uu___132_6382.sigtab);
      is_pattern = (uu___132_6382.is_pattern);
      instantiate_imp = (uu___132_6382.instantiate_imp);
      effects = (uu___132_6382.effects);
      generalize = (uu___132_6382.generalize);
      letrecs = (uu___132_6382.letrecs);
      top_level = (uu___132_6382.top_level);
      check_uvars = (uu___132_6382.check_uvars);
      use_eq = (uu___132_6382.use_eq);
      is_iface = (uu___132_6382.is_iface);
      admit = (uu___132_6382.admit);
      lax = (uu___132_6382.lax);
      lax_universes = (uu___132_6382.lax_universes);
      type_of = (uu___132_6382.type_of);
      universe_of = (uu___132_6382.universe_of);
      use_bv_sorts = (uu___132_6382.use_bv_sorts);
      qname_and_index = (uu___132_6382.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6391::rest ->
        let uu___133_6394 = e in
        {
          solver = (uu___133_6394.solver);
          range = (uu___133_6394.range);
          curmodule = (uu___133_6394.curmodule);
          gamma = (uu___133_6394.gamma);
          gamma_cache = (uu___133_6394.gamma_cache);
          modules = (uu___133_6394.modules);
          expected_typ = (uu___133_6394.expected_typ);
          sigtab = (uu___133_6394.sigtab);
          is_pattern = (uu___133_6394.is_pattern);
          instantiate_imp = (uu___133_6394.instantiate_imp);
          effects = (uu___133_6394.effects);
          generalize = (uu___133_6394.generalize);
          letrecs = (uu___133_6394.letrecs);
          top_level = (uu___133_6394.top_level);
          check_uvars = (uu___133_6394.check_uvars);
          use_eq = (uu___133_6394.use_eq);
          is_iface = (uu___133_6394.is_iface);
          admit = (uu___133_6394.admit);
          lax = (uu___133_6394.lax);
          lax_universes = (uu___133_6394.lax_universes);
          type_of = (uu___133_6394.type_of);
          universe_of = (uu___133_6394.universe_of);
          use_bv_sorts = (uu___133_6394.use_bv_sorts);
          qname_and_index = (uu___133_6394.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6404 = e in
      {
        solver = (uu___134_6404.solver);
        range = (uu___134_6404.range);
        curmodule = (uu___134_6404.curmodule);
        gamma = (uu___134_6404.gamma);
        gamma_cache = (uu___134_6404.gamma_cache);
        modules = (uu___134_6404.modules);
        expected_typ = (uu___134_6404.expected_typ);
        sigtab = (uu___134_6404.sigtab);
        is_pattern = (uu___134_6404.is_pattern);
        instantiate_imp = (uu___134_6404.instantiate_imp);
        effects = (uu___134_6404.effects);
        generalize = (uu___134_6404.generalize);
        letrecs = (uu___134_6404.letrecs);
        top_level = (uu___134_6404.top_level);
        check_uvars = (uu___134_6404.check_uvars);
        use_eq = (uu___134_6404.use_eq);
        is_iface = (uu___134_6404.is_iface);
        admit = (uu___134_6404.admit);
        lax = (uu___134_6404.lax);
        lax_universes = (uu___134_6404.lax_universes);
        type_of = (uu___134_6404.type_of);
        universe_of = (uu___134_6404.universe_of);
        use_bv_sorts = (uu___134_6404.use_bv_sorts);
        qname_and_index = (uu___134_6404.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6422 =
        FStar_List.map
          (fun fpns  ->
             let uu____6433 =
               let uu____6434 =
                 let uu____6435 =
                   FStar_List.map
                     (fun uu____6440  ->
                        match uu____6440 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6435 in
               Prims.strcat uu____6434 "]" in
             Prims.strcat "[" uu____6433) pns in
      FStar_String.concat ";" uu____6422 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6449  -> ());
    push = (fun uu____6450  -> ());
    pop = (fun uu____6451  -> ());
    mark = (fun uu____6452  -> ());
    reset_mark = (fun uu____6453  -> ());
    commit_mark = (fun uu____6454  -> ());
    encode_modul = (fun uu____6455  -> fun uu____6456  -> ());
    encode_sig = (fun uu____6457  -> fun uu____6458  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6465  -> fun uu____6466  -> fun uu____6467  -> ());
    is_trivial = (fun uu____6471  -> fun uu____6472  -> false);
    finish = (fun uu____6473  -> ());
    refresh = (fun uu____6474  -> ())
  }