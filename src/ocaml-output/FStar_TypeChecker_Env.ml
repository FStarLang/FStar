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
          let uu____1533 = FStar_Syntax_Subst.subst vs t in (us, uu____1533)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1538  ->
    match uu___100_1538 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1552  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1562 = inst_tscheme t in
      match uu____1562 with
      | (us,t1) ->
          let uu____1569 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1569)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1581  ->
          match uu____1581 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1599 =
                         let uu____1600 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1605 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1610 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1611 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1600 uu____1605 uu____1610 uu____1611 in
                       failwith uu____1599)
                    else ();
                    (let uu____1613 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1613))
               | uu____1617 ->
                   let uu____1618 =
                     let uu____1619 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1619 in
                   failwith uu____1618)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1623 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1627 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1631 -> false
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
             | ([],uu____1657) -> Maybe
             | (uu____1661,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1673 -> No in
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
          let uu____1733 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1733 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1754  ->
                   match uu___101_1754 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1777 =
                           let uu____1787 =
                             let uu____1795 = inst_tscheme t in
                             FStar_Util.Inl uu____1795 in
                           (uu____1787, (FStar_Ident.range_of_lid l)) in
                         Some uu____1777
                       else None
                   | Binding_sig
                       (uu____1829,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1831);
                                     FStar_Syntax_Syntax.sigrng = uu____1832;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1833;
                                     FStar_Syntax_Syntax.sigmeta = uu____1834;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1843 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1843
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1870 ->
                             Some t
                         | uu____1874 -> cache t in
                       let uu____1875 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1875 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1915 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1915 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1959 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2001 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____2001
         then
           let uu____2012 = find_in_sigtab env lid in
           match uu____2012 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2078) ->
          add_sigelts env ses
      | uu____2083 ->
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
            | uu____2092 -> ()))
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
        (fun uu___102_2110  ->
           match uu___102_2110 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2123 -> None)
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
          ((uu____2144,lb::[]),uu____2146,uu____2147) ->
          let uu____2156 =
            let uu____2161 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2167 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2161, uu____2167) in
          Some uu____2156
      | FStar_Syntax_Syntax.Sig_let ((uu____2174,lbs),uu____2176,uu____2177)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2197 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2204 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2204
                   then
                     let uu____2210 =
                       let uu____2215 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2221 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2215, uu____2221) in
                     Some uu____2210
                   else None)
      | uu____2233 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2252 =
          let uu____2257 =
            let uu____2260 =
              let uu____2261 =
                let uu____2264 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2264 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2261) in
            inst_tscheme uu____2260 in
          (uu____2257, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2252
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2278,uu____2279) ->
        let uu____2282 =
          let uu____2287 =
            let uu____2290 =
              let uu____2291 =
                let uu____2294 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2294 in
              (us, uu____2291) in
            inst_tscheme uu____2290 in
          (uu____2287, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2282
    | uu____2305 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2340 =
        match uu____2340 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2390,uvs,t,uu____2393,uu____2394,uu____2395);
                    FStar_Syntax_Syntax.sigrng = uu____2396;
                    FStar_Syntax_Syntax.sigquals = uu____2397;
                    FStar_Syntax_Syntax.sigmeta = uu____2398;_},None
                  )
                 ->
                 let uu____2408 =
                   let uu____2413 = inst_tscheme (uvs, t) in
                   (uu____2413, rng) in
                 Some uu____2408
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2425;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2427;_},None
                  )
                 ->
                 let uu____2435 =
                   let uu____2436 = in_cur_mod env l in uu____2436 = Yes in
                 if uu____2435
                 then
                   let uu____2442 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2442
                    then
                      let uu____2449 =
                        let uu____2454 = inst_tscheme (uvs, t) in
                        (uu____2454, rng) in
                      Some uu____2449
                    else None)
                 else
                   (let uu____2469 =
                      let uu____2474 = inst_tscheme (uvs, t) in
                      (uu____2474, rng) in
                    Some uu____2469)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2487,uu____2488);
                    FStar_Syntax_Syntax.sigrng = uu____2489;
                    FStar_Syntax_Syntax.sigquals = uu____2490;
                    FStar_Syntax_Syntax.sigmeta = uu____2491;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2510 =
                        let uu____2515 = inst_tscheme (uvs, k) in
                        (uu____2515, rng) in
                      Some uu____2510
                  | uu____2524 ->
                      let uu____2525 =
                        let uu____2530 =
                          let uu____2533 =
                            let uu____2534 =
                              let uu____2537 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2537 in
                            (uvs, uu____2534) in
                          inst_tscheme uu____2533 in
                        (uu____2530, rng) in
                      Some uu____2525)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2552,uu____2553);
                    FStar_Syntax_Syntax.sigrng = uu____2554;
                    FStar_Syntax_Syntax.sigquals = uu____2555;
                    FStar_Syntax_Syntax.sigmeta = uu____2556;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2576 =
                        let uu____2581 = inst_tscheme_with (uvs, k) us in
                        (uu____2581, rng) in
                      Some uu____2576
                  | uu____2590 ->
                      let uu____2591 =
                        let uu____2596 =
                          let uu____2599 =
                            let uu____2600 =
                              let uu____2603 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2603 in
                            (uvs, uu____2600) in
                          inst_tscheme_with uu____2599 us in
                        (uu____2596, rng) in
                      Some uu____2591)
             | FStar_Util.Inr se ->
                 let uu____2623 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2634;
                        FStar_Syntax_Syntax.sigrng = uu____2635;
                        FStar_Syntax_Syntax.sigquals = uu____2636;
                        FStar_Syntax_Syntax.sigmeta = uu____2637;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2646 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2623
                   (FStar_Util.map_option
                      (fun uu____2669  ->
                         match uu____2669 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2686 =
        let uu____2692 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2692 mapper in
      match uu____2686 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2744 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2744.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2744.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2744.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2765 = lookup_qname env l in
      match uu____2765 with | None  -> false | Some uu____2785 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2813 = try_lookup_bv env bv in
      match uu____2813 with
      | None  ->
          let uu____2821 =
            let uu____2822 =
              let uu____2825 = variable_not_found bv in (uu____2825, bvr) in
            FStar_Errors.Error uu____2822 in
          raise uu____2821
      | Some (t,r) ->
          let uu____2832 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2833 = FStar_Range.set_use_range r bvr in
          (uu____2832, uu____2833)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2845 = try_lookup_lid_aux env l in
      match uu____2845 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2887 =
            let uu____2892 =
              let uu____2895 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2895) in
            (uu____2892, r1) in
          Some uu____2887
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2912 = try_lookup_lid env l in
      match uu____2912 with
      | None  ->
          let uu____2926 =
            let uu____2927 =
              let uu____2930 = name_not_found l in
              (uu____2930, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2927 in
          raise uu____2926
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2951  ->
              match uu___103_2951 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2953 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2964 = lookup_qname env lid in
      match uu____2964 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2979,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2982;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2984;_},None
            ),uu____2985)
          ->
          let uu____3009 =
            let uu____3015 =
              let uu____3018 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____3018) in
            (uu____3015, q) in
          Some uu____3009
      | uu____3027 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3049 = lookup_qname env lid in
      match uu____3049 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3062,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3065;
              FStar_Syntax_Syntax.sigquals = uu____3066;
              FStar_Syntax_Syntax.sigmeta = uu____3067;_},None
            ),uu____3068)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3092 ->
          let uu____3103 =
            let uu____3104 =
              let uu____3107 = name_not_found lid in
              (uu____3107, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3104 in
          raise uu____3103
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3118 = lookup_qname env lid in
      match uu____3118 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3131,uvs,t,uu____3134,uu____3135,uu____3136);
              FStar_Syntax_Syntax.sigrng = uu____3137;
              FStar_Syntax_Syntax.sigquals = uu____3138;
              FStar_Syntax_Syntax.sigmeta = uu____3139;_},None
            ),uu____3140)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3166 ->
          let uu____3177 =
            let uu____3178 =
              let uu____3181 = name_not_found lid in
              (uu____3181, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3178 in
          raise uu____3177
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3193 = lookup_qname env lid in
      match uu____3193 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3207,uu____3208,uu____3209,uu____3210,uu____3211,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3213;
              FStar_Syntax_Syntax.sigquals = uu____3214;
              FStar_Syntax_Syntax.sigmeta = uu____3215;_},uu____3216),uu____3217)
          -> (true, dcs)
      | uu____3247 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3265 = lookup_qname env lid in
      match uu____3265 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3276,uu____3277,uu____3278,l,uu____3280,uu____3281);
              FStar_Syntax_Syntax.sigrng = uu____3282;
              FStar_Syntax_Syntax.sigquals = uu____3283;
              FStar_Syntax_Syntax.sigmeta = uu____3284;_},uu____3285),uu____3286)
          -> l
      | uu____3313 ->
          let uu____3324 =
            let uu____3325 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3325 in
          failwith uu____3324
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
        let uu____3349 = lookup_qname env lid in
        match uu____3349 with
        | Some (FStar_Util.Inr (se,None ),uu____3364) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3390,lbs),uu____3392,uu____3393) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3410 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3410
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3431 -> None)
        | uu____3434 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3455 = lookup_qname env ftv in
      match uu____3455 with
      | Some (FStar_Util.Inr (se,None ),uu____3468) ->
          let uu____3491 = effect_signature se in
          (match uu____3491 with
           | None  -> None
           | Some ((uu____3502,t),r) ->
               let uu____3511 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3511)
      | uu____3512 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3529 = try_lookup_effect_lid env ftv in
      match uu____3529 with
      | None  ->
          let uu____3531 =
            let uu____3532 =
              let uu____3535 = name_not_found ftv in
              (uu____3535, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3532 in
          raise uu____3531
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
        let uu____3549 = lookup_qname env lid0 in
        match uu____3549 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3567);
                FStar_Syntax_Syntax.sigrng = uu____3568;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3570;_},None
              ),uu____3571)
            ->
            let lid1 =
              let uu____3598 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3598 in
            let uu____3599 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3601  ->
                      match uu___104_3601 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3602 -> false)) in
            if uu____3599
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
                     (let uu____3624 =
                        let uu____3625 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3626 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3625 uu____3626 in
                      failwith uu____3624) in
               match (binders, univs1) with
               | ([],uu____3634) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3643,uu____3644::uu____3645::uu____3646) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3649 =
                     let uu____3650 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3651 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3650 uu____3651 in
                   failwith uu____3649
               | uu____3659 ->
                   let uu____3662 =
                     let uu____3665 =
                       let uu____3666 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3666) in
                     inst_tscheme_with uu____3665 insts in
                   (match uu____3662 with
                    | (uu____3674,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3677 =
                          let uu____3678 = FStar_Syntax_Subst.compress t1 in
                          uu____3678.FStar_Syntax_Syntax.n in
                        (match uu____3677 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3708 -> failwith "Impossible")))
        | uu____3712 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3738 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3738 with
        | None  -> None
        | Some (uu____3745,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3750 = find1 l2 in
            (match uu____3750 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3755 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3755 with
        | Some l1 -> l1
        | None  ->
            let uu____3758 = find1 l in
            (match uu____3758 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3770 = lookup_qname env l1 in
      match uu____3770 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3782;
              FStar_Syntax_Syntax.sigrng = uu____3783;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3785;_},uu____3786),uu____3787)
          -> q
      | uu____3812 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3835 =
          let uu____3836 =
            let uu____3837 = FStar_Util.string_of_int i in
            let uu____3838 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3837 uu____3838 in
          failwith uu____3836 in
        let uu____3839 = lookup_datacon env lid in
        match uu____3839 with
        | (uu____3842,t) ->
            let uu____3844 =
              let uu____3845 = FStar_Syntax_Subst.compress t in
              uu____3845.FStar_Syntax_Syntax.n in
            (match uu____3844 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3849) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3872 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3872 FStar_Pervasives.fst)
             | uu____3877 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3884 = lookup_qname env l in
      match uu____3884 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3895,uu____3896,uu____3897);
              FStar_Syntax_Syntax.sigrng = uu____3898;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3900;_},uu____3901),uu____3902)
          ->
          FStar_Util.for_some
            (fun uu___105_3927  ->
               match uu___105_3927 with
               | FStar_Syntax_Syntax.Projector uu____3928 -> true
               | uu____3931 -> false) quals
      | uu____3932 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3949 = lookup_qname env lid in
      match uu____3949 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3960,uu____3961,uu____3962,uu____3963,uu____3964,uu____3965);
              FStar_Syntax_Syntax.sigrng = uu____3966;
              FStar_Syntax_Syntax.sigquals = uu____3967;
              FStar_Syntax_Syntax.sigmeta = uu____3968;_},uu____3969),uu____3970)
          -> true
      | uu____3997 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4014 = lookup_qname env lid in
      match uu____4014 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4025,uu____4026,uu____4027,uu____4028,uu____4029,uu____4030);
              FStar_Syntax_Syntax.sigrng = uu____4031;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4033;_},uu____4034),uu____4035)
          ->
          FStar_Util.for_some
            (fun uu___106_4064  ->
               match uu___106_4064 with
               | FStar_Syntax_Syntax.RecordType uu____4065 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4070 -> true
               | uu____4075 -> false) quals
      | uu____4076 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4093 = lookup_qname env lid in
      match uu____4093 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4104,uu____4105,uu____4106);
              FStar_Syntax_Syntax.sigrng = uu____4107;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4109;_},uu____4110),uu____4111)
          ->
          FStar_Util.for_some
            (fun uu___107_4140  ->
               match uu___107_4140 with
               | FStar_Syntax_Syntax.Action uu____4141 -> true
               | uu____4142 -> false) quals
      | uu____4143 -> false
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
      let uu____4162 =
        let uu____4163 = FStar_Syntax_Util.un_uinst head1 in
        uu____4163.FStar_Syntax_Syntax.n in
      match uu____4162 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4167 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4205 -> Some false
        | FStar_Util.Inr (se,uu____4214) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4223 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4227 -> Some true
             | uu____4236 -> Some false) in
      let uu____4237 =
        let uu____4239 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4239 mapper in
      match uu____4237 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4266 = lookup_qname env lid in
      match uu____4266 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4277,uu____4278,tps,uu____4280,uu____4281,uu____4282);
              FStar_Syntax_Syntax.sigrng = uu____4283;
              FStar_Syntax_Syntax.sigquals = uu____4284;
              FStar_Syntax_Syntax.sigmeta = uu____4285;_},uu____4286),uu____4287)
          -> FStar_List.length tps
      | uu____4320 ->
          let uu____4331 =
            let uu____4332 =
              let uu____4335 = name_not_found lid in
              (uu____4335, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4332 in
          raise uu____4331
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
           (fun uu____4357  ->
              match uu____4357 with
              | (d,uu____4362) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4371 = effect_decl_opt env l in
      match uu____4371 with
      | None  ->
          let uu____4379 =
            let uu____4380 =
              let uu____4383 = name_not_found l in
              (uu____4383, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4380 in
          raise uu____4379
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
            (let uu____4426 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4450  ->
                       match uu____4450 with
                       | (m1,m2,uu____4458,uu____4459,uu____4460) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4426 with
             | None  ->
                 let uu____4469 =
                   let uu____4470 =
                     let uu____4473 =
                       let uu____4474 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4475 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4474
                         uu____4475 in
                     (uu____4473, (env.range)) in
                   FStar_Errors.Error uu____4470 in
                 raise uu____4469
             | Some (uu____4479,uu____4480,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4527 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4539  ->
            match uu____4539 with
            | (d,uu____4543) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4527 with
  | None  ->
      let uu____4550 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4550
  | Some (md,_q) ->
      let uu____4559 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4559 with
       | (uu____4566,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4574)::(wp,uu____4576)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4598 -> failwith "Impossible"))
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
                 let uu____4634 = get_range env in
                 let uu____4635 =
                   let uu____4638 =
                     let uu____4639 =
                       let uu____4649 =
                         let uu____4651 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4651] in
                       (null_wp, uu____4649) in
                     FStar_Syntax_Syntax.Tm_app uu____4639 in
                   FStar_Syntax_Syntax.mk uu____4638 in
                 uu____4635 None uu____4634 in
               let uu____4661 =
                 let uu____4662 =
                   let uu____4668 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4668] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4662;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4661)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4677 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4677.order);
              joins = (uu___118_4677.joins)
            } in
          let uu___119_4682 = env in
          {
            solver = (uu___119_4682.solver);
            range = (uu___119_4682.range);
            curmodule = (uu___119_4682.curmodule);
            gamma = (uu___119_4682.gamma);
            gamma_cache = (uu___119_4682.gamma_cache);
            modules = (uu___119_4682.modules);
            expected_typ = (uu___119_4682.expected_typ);
            sigtab = (uu___119_4682.sigtab);
            is_pattern = (uu___119_4682.is_pattern);
            instantiate_imp = (uu___119_4682.instantiate_imp);
            effects;
            generalize = (uu___119_4682.generalize);
            letrecs = (uu___119_4682.letrecs);
            top_level = (uu___119_4682.top_level);
            check_uvars = (uu___119_4682.check_uvars);
            use_eq = (uu___119_4682.use_eq);
            is_iface = (uu___119_4682.is_iface);
            admit = (uu___119_4682.admit);
            lax = (uu___119_4682.lax);
            lax_universes = (uu___119_4682.lax_universes);
            type_of = (uu___119_4682.type_of);
            universe_of = (uu___119_4682.universe_of);
            use_bv_sorts = (uu___119_4682.use_bv_sorts);
            qname_and_index = (uu___119_4682.qname_and_index);
            proof_ns = (uu___119_4682.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4699 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4699 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4778 = (e1.mlift).mlift_wp t wp in
                              let uu____4779 = l1 t wp e in
                              l2 t uu____4778 uu____4779))
                | uu____4780 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4815 = inst_tscheme lift_t in
            match uu____4815 with
            | (uu____4820,lift_t1) ->
                let uu____4822 =
                  let uu____4825 =
                    let uu____4826 =
                      let uu____4836 =
                        let uu____4838 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4839 =
                          let uu____4841 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4841] in
                        uu____4838 :: uu____4839 in
                      (lift_t1, uu____4836) in
                    FStar_Syntax_Syntax.Tm_app uu____4826 in
                  FStar_Syntax_Syntax.mk uu____4825 in
                uu____4822 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4886 = inst_tscheme lift_t in
            match uu____4886 with
            | (uu____4891,lift_t1) ->
                let uu____4893 =
                  let uu____4896 =
                    let uu____4897 =
                      let uu____4907 =
                        let uu____4909 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4910 =
                          let uu____4912 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4913 =
                            let uu____4915 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4915] in
                          uu____4912 :: uu____4913 in
                        uu____4909 :: uu____4910 in
                      (lift_t1, uu____4907) in
                    FStar_Syntax_Syntax.Tm_app uu____4897 in
                  FStar_Syntax_Syntax.mk uu____4896 in
                uu____4893 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4956 =
                let uu____4957 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4957
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4956 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4961 =
              let uu____4962 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4962 in
            let uu____4963 =
              let uu____4964 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4979 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4979) in
              FStar_Util.dflt "none" uu____4964 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4961
              uu____4963 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4992  ->
                    match uu____4992 with
                    | (e,uu____4997) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____5010 =
            match uu____5010 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_39  -> Some _0_39)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____5035 =
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
                                    (let uu____5047 =
                                       let uu____5052 =
                                         find_edge order1 (i, k) in
                                       let uu____5054 =
                                         find_edge order1 (k, j) in
                                       (uu____5052, uu____5054) in
                                     match uu____5047 with
                                     | (Some e1,Some e2) ->
                                         let uu____5063 = compose_edges e1 e2 in
                                         [uu____5063]
                                     | uu____5064 -> []))))) in
              FStar_List.append order1 uu____5035 in
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
                   let uu____5079 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5080 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5080
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5079
                   then
                     let uu____5083 =
                       let uu____5084 =
                         let uu____5087 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5088 = get_range env in
                         (uu____5087, uu____5088) in
                       FStar_Errors.Error uu____5084 in
                     raise uu____5083
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
                                            let uu____5151 =
                                              let uu____5156 =
                                                find_edge order2 (i, k) in
                                              let uu____5158 =
                                                find_edge order2 (j, k) in
                                              (uu____5156, uu____5158) in
                                            match uu____5151 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5181,uu____5182)
                                                     ->
                                                     let uu____5186 =
                                                       let uu____5189 =
                                                         let uu____5190 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5190 in
                                                       let uu____5192 =
                                                         let uu____5193 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5193 in
                                                       (uu____5189,
                                                         uu____5192) in
                                                     (match uu____5186 with
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
                                            | uu____5212 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5251 = env.effects in
              { decls = (uu___120_5251.decls); order = order2; joins } in
            let uu___121_5252 = env in
            {
              solver = (uu___121_5252.solver);
              range = (uu___121_5252.range);
              curmodule = (uu___121_5252.curmodule);
              gamma = (uu___121_5252.gamma);
              gamma_cache = (uu___121_5252.gamma_cache);
              modules = (uu___121_5252.modules);
              expected_typ = (uu___121_5252.expected_typ);
              sigtab = (uu___121_5252.sigtab);
              is_pattern = (uu___121_5252.is_pattern);
              instantiate_imp = (uu___121_5252.instantiate_imp);
              effects;
              generalize = (uu___121_5252.generalize);
              letrecs = (uu___121_5252.letrecs);
              top_level = (uu___121_5252.top_level);
              check_uvars = (uu___121_5252.check_uvars);
              use_eq = (uu___121_5252.use_eq);
              is_iface = (uu___121_5252.is_iface);
              admit = (uu___121_5252.admit);
              lax = (uu___121_5252.lax);
              lax_universes = (uu___121_5252.lax_universes);
              type_of = (uu___121_5252.type_of);
              universe_of = (uu___121_5252.universe_of);
              use_bv_sorts = (uu___121_5252.use_bv_sorts);
              qname_and_index = (uu___121_5252.qname_and_index);
              proof_ns = (uu___121_5252.proof_ns)
            }))
      | uu____5253 -> env
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
        | uu____5275 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5283 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5283 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5293 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5293 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5315 =
                     let uu____5316 =
                       let uu____5319 =
                         let uu____5320 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5329 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5340 =
                           let uu____5341 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5341 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5320 uu____5329 uu____5340 in
                       (uu____5319, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5316 in
                   raise uu____5315)
                else ();
                (let inst1 =
                   let uu____5345 =
                     let uu____5351 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5351 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5358  ->
                        fun uu____5359  ->
                          match (uu____5358, uu____5359) with
                          | ((x,uu____5373),(t,uu____5375)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5345 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5390 =
                     let uu___122_5391 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5391.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5391.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5391.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5391.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5390
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5421 =
    let uu____5426 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5426 in
  match uu____5421 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5442 =
        only_reifiable &&
          (let uu____5443 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5443) in
      if uu____5442
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5456 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5458 =
               let uu____5467 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5467) in
             (match uu____5458 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5501 =
                    let uu____5504 = get_range env in
                    let uu____5505 =
                      let uu____5508 =
                        let uu____5509 =
                          let uu____5519 =
                            let uu____5521 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5521; wp] in
                          (repr, uu____5519) in
                        FStar_Syntax_Syntax.Tm_app uu____5509 in
                      FStar_Syntax_Syntax.mk uu____5508 in
                    uu____5505 None uu____5504 in
                  Some uu____5501))
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
          let uu____5565 =
            let uu____5566 =
              let uu____5569 =
                let uu____5570 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5570 in
              let uu____5571 = get_range env in (uu____5569, uu____5571) in
            FStar_Errors.Error uu____5566 in
          raise uu____5565 in
        let uu____5572 = effect_repr_aux true env c u_c in
        match uu____5572 with
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
        | FStar_Util.Inr (eff_name,uu____5604) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5617 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5624 =
        let uu____5625 = FStar_Syntax_Subst.compress t in
        uu____5625.FStar_Syntax_Syntax.n in
      match uu____5624 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5628,c) ->
          is_reifiable_comp env c
      | uu____5640 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5658)::uu____5659 -> x :: rest
        | (Binding_sig_inst uu____5664)::uu____5665 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5674 = push1 x rest1 in local :: uu____5674 in
      let uu___123_5676 = env in
      let uu____5677 = push1 s env.gamma in
      {
        solver = (uu___123_5676.solver);
        range = (uu___123_5676.range);
        curmodule = (uu___123_5676.curmodule);
        gamma = uu____5677;
        gamma_cache = (uu___123_5676.gamma_cache);
        modules = (uu___123_5676.modules);
        expected_typ = (uu___123_5676.expected_typ);
        sigtab = (uu___123_5676.sigtab);
        is_pattern = (uu___123_5676.is_pattern);
        instantiate_imp = (uu___123_5676.instantiate_imp);
        effects = (uu___123_5676.effects);
        generalize = (uu___123_5676.generalize);
        letrecs = (uu___123_5676.letrecs);
        top_level = (uu___123_5676.top_level);
        check_uvars = (uu___123_5676.check_uvars);
        use_eq = (uu___123_5676.use_eq);
        is_iface = (uu___123_5676.is_iface);
        admit = (uu___123_5676.admit);
        lax = (uu___123_5676.lax);
        lax_universes = (uu___123_5676.lax_universes);
        type_of = (uu___123_5676.type_of);
        universe_of = (uu___123_5676.universe_of);
        use_bv_sorts = (uu___123_5676.use_bv_sorts);
        qname_and_index = (uu___123_5676.qname_and_index);
        proof_ns = (uu___123_5676.proof_ns)
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
      let uu___124_5704 = env in
      {
        solver = (uu___124_5704.solver);
        range = (uu___124_5704.range);
        curmodule = (uu___124_5704.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5704.gamma_cache);
        modules = (uu___124_5704.modules);
        expected_typ = (uu___124_5704.expected_typ);
        sigtab = (uu___124_5704.sigtab);
        is_pattern = (uu___124_5704.is_pattern);
        instantiate_imp = (uu___124_5704.instantiate_imp);
        effects = (uu___124_5704.effects);
        generalize = (uu___124_5704.generalize);
        letrecs = (uu___124_5704.letrecs);
        top_level = (uu___124_5704.top_level);
        check_uvars = (uu___124_5704.check_uvars);
        use_eq = (uu___124_5704.use_eq);
        is_iface = (uu___124_5704.is_iface);
        admit = (uu___124_5704.admit);
        lax = (uu___124_5704.lax);
        lax_universes = (uu___124_5704.lax_universes);
        type_of = (uu___124_5704.type_of);
        universe_of = (uu___124_5704.universe_of);
        use_bv_sorts = (uu___124_5704.use_bv_sorts);
        qname_and_index = (uu___124_5704.qname_and_index);
        proof_ns = (uu___124_5704.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5725 = env in
             {
               solver = (uu___125_5725.solver);
               range = (uu___125_5725.range);
               curmodule = (uu___125_5725.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5725.gamma_cache);
               modules = (uu___125_5725.modules);
               expected_typ = (uu___125_5725.expected_typ);
               sigtab = (uu___125_5725.sigtab);
               is_pattern = (uu___125_5725.is_pattern);
               instantiate_imp = (uu___125_5725.instantiate_imp);
               effects = (uu___125_5725.effects);
               generalize = (uu___125_5725.generalize);
               letrecs = (uu___125_5725.letrecs);
               top_level = (uu___125_5725.top_level);
               check_uvars = (uu___125_5725.check_uvars);
               use_eq = (uu___125_5725.use_eq);
               is_iface = (uu___125_5725.is_iface);
               admit = (uu___125_5725.admit);
               lax = (uu___125_5725.lax);
               lax_universes = (uu___125_5725.lax_universes);
               type_of = (uu___125_5725.type_of);
               universe_of = (uu___125_5725.universe_of);
               use_bv_sorts = (uu___125_5725.use_bv_sorts);
               qname_and_index = (uu___125_5725.qname_and_index);
               proof_ns = (uu___125_5725.proof_ns)
             }))
    | uu____5726 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5739  ->
             match uu____5739 with | (x,uu____5743) -> push_bv env1 x) env bs
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
            let uu___126_5763 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5763.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5763.FStar_Syntax_Syntax.index);
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
      (let uu___127_5793 = env in
       {
         solver = (uu___127_5793.solver);
         range = (uu___127_5793.range);
         curmodule = (uu___127_5793.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5793.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5793.sigtab);
         is_pattern = (uu___127_5793.is_pattern);
         instantiate_imp = (uu___127_5793.instantiate_imp);
         effects = (uu___127_5793.effects);
         generalize = (uu___127_5793.generalize);
         letrecs = (uu___127_5793.letrecs);
         top_level = (uu___127_5793.top_level);
         check_uvars = (uu___127_5793.check_uvars);
         use_eq = (uu___127_5793.use_eq);
         is_iface = (uu___127_5793.is_iface);
         admit = (uu___127_5793.admit);
         lax = (uu___127_5793.lax);
         lax_universes = (uu___127_5793.lax_universes);
         type_of = (uu___127_5793.type_of);
         universe_of = (uu___127_5793.universe_of);
         use_bv_sorts = (uu___127_5793.use_bv_sorts);
         qname_and_index = (uu___127_5793.qname_and_index);
         proof_ns = (uu___127_5793.proof_ns)
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
        let uu____5817 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5817 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5833 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5833)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5843 = env in
      {
        solver = (uu___128_5843.solver);
        range = (uu___128_5843.range);
        curmodule = (uu___128_5843.curmodule);
        gamma = (uu___128_5843.gamma);
        gamma_cache = (uu___128_5843.gamma_cache);
        modules = (uu___128_5843.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5843.sigtab);
        is_pattern = (uu___128_5843.is_pattern);
        instantiate_imp = (uu___128_5843.instantiate_imp);
        effects = (uu___128_5843.effects);
        generalize = (uu___128_5843.generalize);
        letrecs = (uu___128_5843.letrecs);
        top_level = (uu___128_5843.top_level);
        check_uvars = (uu___128_5843.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5843.is_iface);
        admit = (uu___128_5843.admit);
        lax = (uu___128_5843.lax);
        lax_universes = (uu___128_5843.lax_universes);
        type_of = (uu___128_5843.type_of);
        universe_of = (uu___128_5843.universe_of);
        use_bv_sorts = (uu___128_5843.use_bv_sorts);
        qname_and_index = (uu___128_5843.qname_and_index);
        proof_ns = (uu___128_5843.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5859 = expected_typ env_ in
    ((let uu___129_5862 = env_ in
      {
        solver = (uu___129_5862.solver);
        range = (uu___129_5862.range);
        curmodule = (uu___129_5862.curmodule);
        gamma = (uu___129_5862.gamma);
        gamma_cache = (uu___129_5862.gamma_cache);
        modules = (uu___129_5862.modules);
        expected_typ = None;
        sigtab = (uu___129_5862.sigtab);
        is_pattern = (uu___129_5862.is_pattern);
        instantiate_imp = (uu___129_5862.instantiate_imp);
        effects = (uu___129_5862.effects);
        generalize = (uu___129_5862.generalize);
        letrecs = (uu___129_5862.letrecs);
        top_level = (uu___129_5862.top_level);
        check_uvars = (uu___129_5862.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5862.is_iface);
        admit = (uu___129_5862.admit);
        lax = (uu___129_5862.lax);
        lax_universes = (uu___129_5862.lax_universes);
        type_of = (uu___129_5862.type_of);
        universe_of = (uu___129_5862.universe_of);
        use_bv_sorts = (uu___129_5862.use_bv_sorts);
        qname_and_index = (uu___129_5862.qname_and_index);
        proof_ns = (uu___129_5862.proof_ns)
      }), uu____5859)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5873 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5877  ->
                    match uu___108_5877 with
                    | Binding_sig (uu____5879,se) -> [se]
                    | uu____5883 -> [])) in
          FStar_All.pipe_right uu____5873 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5888 = env in
       {
         solver = (uu___130_5888.solver);
         range = (uu___130_5888.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5888.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5888.expected_typ);
         sigtab = (uu___130_5888.sigtab);
         is_pattern = (uu___130_5888.is_pattern);
         instantiate_imp = (uu___130_5888.instantiate_imp);
         effects = (uu___130_5888.effects);
         generalize = (uu___130_5888.generalize);
         letrecs = (uu___130_5888.letrecs);
         top_level = (uu___130_5888.top_level);
         check_uvars = (uu___130_5888.check_uvars);
         use_eq = (uu___130_5888.use_eq);
         is_iface = (uu___130_5888.is_iface);
         admit = (uu___130_5888.admit);
         lax = (uu___130_5888.lax);
         lax_universes = (uu___130_5888.lax_universes);
         type_of = (uu___130_5888.type_of);
         universe_of = (uu___130_5888.universe_of);
         use_bv_sorts = (uu___130_5888.use_bv_sorts);
         qname_and_index = (uu___130_5888.qname_and_index);
         proof_ns = (uu___130_5888.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5938)::tl1 -> aux out tl1
      | (Binding_lid (uu____5941,(uu____5942,t)))::tl1 ->
          let uu____5951 =
            let uu____5955 = FStar_Syntax_Free.uvars t in ext out uu____5955 in
          aux uu____5951 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5959;
            FStar_Syntax_Syntax.index = uu____5960;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5966 =
            let uu____5970 = FStar_Syntax_Free.uvars t in ext out uu____5970 in
          aux uu____5966 tl1
      | (Binding_sig uu____5974)::uu____5975 -> out
      | (Binding_sig_inst uu____5980)::uu____5981 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6018)::tl1 -> aux out tl1
      | (Binding_univ uu____6025)::tl1 -> aux out tl1
      | (Binding_lid (uu____6028,(uu____6029,t)))::tl1 ->
          let uu____6038 =
            let uu____6040 = FStar_Syntax_Free.univs t in ext out uu____6040 in
          aux uu____6038 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6042;
            FStar_Syntax_Syntax.index = uu____6043;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6049 =
            let uu____6051 = FStar_Syntax_Free.univs t in ext out uu____6051 in
          aux uu____6049 tl1
      | (Binding_sig uu____6053)::uu____6054 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6091)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6101 = FStar_Util.set_add uname out in aux uu____6101 tl1
      | (Binding_lid (uu____6103,(uu____6104,t)))::tl1 ->
          let uu____6113 =
            let uu____6115 = FStar_Syntax_Free.univnames t in
            ext out uu____6115 in
          aux uu____6113 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6117;
            FStar_Syntax_Syntax.index = uu____6118;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6124 =
            let uu____6126 = FStar_Syntax_Free.univnames t in
            ext out uu____6126 in
          aux uu____6124 tl1
      | (Binding_sig uu____6128)::uu____6129 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6145  ->
            match uu___109_6145 with
            | Binding_var x -> [x]
            | Binding_lid uu____6148 -> []
            | Binding_sig uu____6151 -> []
            | Binding_univ uu____6155 -> []
            | Binding_sig_inst uu____6156 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6166 =
      let uu____6168 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6168
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6166 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6184 =
      let uu____6185 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6189  ->
                match uu___110_6189 with
                | Binding_var x ->
                    let uu____6191 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6191
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6194) ->
                    let uu____6195 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6195
                | Binding_sig (ls,uu____6197) ->
                    let uu____6200 =
                      let uu____6201 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6201
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6200
                | Binding_sig_inst (ls,uu____6207,uu____6208) ->
                    let uu____6211 =
                      let uu____6212 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6212
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6211)) in
      FStar_All.pipe_right uu____6185 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6184 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6224 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6224
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6245  ->
                 fun uu____6246  ->
                   match (uu____6245, uu____6246) with
                   | ((b1,uu____6256),(b2,uu____6258)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6301  ->
             match uu___111_6301 with
             | Binding_sig (lids,uu____6305) -> FStar_List.append lids keys
             | uu____6308 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6310  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6335) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6347,uu____6348) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6372 = list_prefix p path1 in
            if uu____6372 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6382 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6382
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6402 = e in
            {
              solver = (uu___131_6402.solver);
              range = (uu___131_6402.range);
              curmodule = (uu___131_6402.curmodule);
              gamma = (uu___131_6402.gamma);
              gamma_cache = (uu___131_6402.gamma_cache);
              modules = (uu___131_6402.modules);
              expected_typ = (uu___131_6402.expected_typ);
              sigtab = (uu___131_6402.sigtab);
              is_pattern = (uu___131_6402.is_pattern);
              instantiate_imp = (uu___131_6402.instantiate_imp);
              effects = (uu___131_6402.effects);
              generalize = (uu___131_6402.generalize);
              letrecs = (uu___131_6402.letrecs);
              top_level = (uu___131_6402.top_level);
              check_uvars = (uu___131_6402.check_uvars);
              use_eq = (uu___131_6402.use_eq);
              is_iface = (uu___131_6402.is_iface);
              admit = (uu___131_6402.admit);
              lax = (uu___131_6402.lax);
              lax_universes = (uu___131_6402.lax_universes);
              type_of = (uu___131_6402.type_of);
              universe_of = (uu___131_6402.universe_of);
              use_bv_sorts = (uu___131_6402.use_bv_sorts);
              qname_and_index = (uu___131_6402.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6421 = e in
    {
      solver = (uu___132_6421.solver);
      range = (uu___132_6421.range);
      curmodule = (uu___132_6421.curmodule);
      gamma = (uu___132_6421.gamma);
      gamma_cache = (uu___132_6421.gamma_cache);
      modules = (uu___132_6421.modules);
      expected_typ = (uu___132_6421.expected_typ);
      sigtab = (uu___132_6421.sigtab);
      is_pattern = (uu___132_6421.is_pattern);
      instantiate_imp = (uu___132_6421.instantiate_imp);
      effects = (uu___132_6421.effects);
      generalize = (uu___132_6421.generalize);
      letrecs = (uu___132_6421.letrecs);
      top_level = (uu___132_6421.top_level);
      check_uvars = (uu___132_6421.check_uvars);
      use_eq = (uu___132_6421.use_eq);
      is_iface = (uu___132_6421.is_iface);
      admit = (uu___132_6421.admit);
      lax = (uu___132_6421.lax);
      lax_universes = (uu___132_6421.lax_universes);
      type_of = (uu___132_6421.type_of);
      universe_of = (uu___132_6421.universe_of);
      use_bv_sorts = (uu___132_6421.use_bv_sorts);
      qname_and_index = (uu___132_6421.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6430::rest ->
        let uu___133_6433 = e in
        {
          solver = (uu___133_6433.solver);
          range = (uu___133_6433.range);
          curmodule = (uu___133_6433.curmodule);
          gamma = (uu___133_6433.gamma);
          gamma_cache = (uu___133_6433.gamma_cache);
          modules = (uu___133_6433.modules);
          expected_typ = (uu___133_6433.expected_typ);
          sigtab = (uu___133_6433.sigtab);
          is_pattern = (uu___133_6433.is_pattern);
          instantiate_imp = (uu___133_6433.instantiate_imp);
          effects = (uu___133_6433.effects);
          generalize = (uu___133_6433.generalize);
          letrecs = (uu___133_6433.letrecs);
          top_level = (uu___133_6433.top_level);
          check_uvars = (uu___133_6433.check_uvars);
          use_eq = (uu___133_6433.use_eq);
          is_iface = (uu___133_6433.is_iface);
          admit = (uu___133_6433.admit);
          lax = (uu___133_6433.lax);
          lax_universes = (uu___133_6433.lax_universes);
          type_of = (uu___133_6433.type_of);
          universe_of = (uu___133_6433.universe_of);
          use_bv_sorts = (uu___133_6433.use_bv_sorts);
          qname_and_index = (uu___133_6433.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6443 = e in
      {
        solver = (uu___134_6443.solver);
        range = (uu___134_6443.range);
        curmodule = (uu___134_6443.curmodule);
        gamma = (uu___134_6443.gamma);
        gamma_cache = (uu___134_6443.gamma_cache);
        modules = (uu___134_6443.modules);
        expected_typ = (uu___134_6443.expected_typ);
        sigtab = (uu___134_6443.sigtab);
        is_pattern = (uu___134_6443.is_pattern);
        instantiate_imp = (uu___134_6443.instantiate_imp);
        effects = (uu___134_6443.effects);
        generalize = (uu___134_6443.generalize);
        letrecs = (uu___134_6443.letrecs);
        top_level = (uu___134_6443.top_level);
        check_uvars = (uu___134_6443.check_uvars);
        use_eq = (uu___134_6443.use_eq);
        is_iface = (uu___134_6443.is_iface);
        admit = (uu___134_6443.admit);
        lax = (uu___134_6443.lax);
        lax_universes = (uu___134_6443.lax_universes);
        type_of = (uu___134_6443.type_of);
        universe_of = (uu___134_6443.universe_of);
        use_bv_sorts = (uu___134_6443.use_bv_sorts);
        qname_and_index = (uu___134_6443.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6461 =
        FStar_List.map
          (fun fpns  ->
             let uu____6472 =
               let uu____6473 =
                 let uu____6474 =
                   FStar_List.map
                     (fun uu____6479  ->
                        match uu____6479 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6474 in
               Prims.strcat uu____6473 "]" in
             Prims.strcat "[" uu____6472) pns in
      FStar_String.concat ";" uu____6461 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6488  -> ());
    push = (fun uu____6489  -> ());
    pop = (fun uu____6490  -> ());
    mark = (fun uu____6491  -> ());
    reset_mark = (fun uu____6492  -> ());
    commit_mark = (fun uu____6493  -> ());
    encode_modul = (fun uu____6494  -> fun uu____6495  -> ());
    encode_sig = (fun uu____6496  -> fun uu____6497  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6504  -> fun uu____6505  -> fun uu____6506  -> ());
    is_trivial = (fun uu____6510  -> fun uu____6511  -> false);
    finish = (fun uu____6512  -> ());
    refresh = (fun uu____6513  -> ())
  }