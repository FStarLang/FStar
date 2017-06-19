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
    match projectee with | Binding_var _0 -> true | uu____35 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____51 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____74 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____97 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____115 -> false
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
    match projectee with | NoDelta  -> true | uu____144 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____149 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____154 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____160 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____173 -> false
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
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;}
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
      | (NoDelta ,uu____1076) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____1077,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____1078,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____1079 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____1091 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____1101 =
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
          let uu____1144 = new_gamma_cache () in
          let uu____1146 = new_sigtab () in
          let uu____1148 =
            let uu____1149 = FStar_Options.using_facts_from () in
            match uu____1149 with
            | Some ns ->
                let uu____1155 =
                  let uu____1160 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____1160 [([], false)] in
                [uu____1155]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1144;
            modules = [];
            expected_typ = None;
            sigtab = uu____1146;
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
            proof_ns = uu____1148;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available")
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1244  ->
    let uu____1245 = FStar_ST.read query_indices in
    match uu____1245 with
    | [] -> failwith "Empty query indices!"
    | uu____1259 ->
        let uu____1264 =
          let uu____1269 =
            let uu____1273 = FStar_ST.read query_indices in
            FStar_List.hd uu____1273 in
          let uu____1287 = FStar_ST.read query_indices in uu____1269 ::
            uu____1287 in
        FStar_ST.write query_indices uu____1264
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1310  ->
    let uu____1311 = FStar_ST.read query_indices in
    match uu____1311 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1348  ->
    match uu____1348 with
    | (l,n1) ->
        let uu____1353 = FStar_ST.read query_indices in
        (match uu____1353 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1387 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1398  ->
    let uu____1399 = FStar_ST.read query_indices in FStar_List.hd uu____1399
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1416  ->
    let uu____1417 = FStar_ST.read query_indices in
    match uu____1417 with
    | hd1::uu____1429::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1456 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1471 =
       let uu____1473 = FStar_ST.read stack in env :: uu____1473 in
     FStar_ST.write stack uu____1471);
    (let uu___112_1481 = env in
     let uu____1482 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1484 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1481.solver);
       range = (uu___112_1481.range);
       curmodule = (uu___112_1481.curmodule);
       gamma = (uu___112_1481.gamma);
       gamma_cache = uu____1482;
       modules = (uu___112_1481.modules);
       expected_typ = (uu___112_1481.expected_typ);
       sigtab = uu____1484;
       is_pattern = (uu___112_1481.is_pattern);
       instantiate_imp = (uu___112_1481.instantiate_imp);
       effects = (uu___112_1481.effects);
       generalize = (uu___112_1481.generalize);
       letrecs = (uu___112_1481.letrecs);
       top_level = (uu___112_1481.top_level);
       check_uvars = (uu___112_1481.check_uvars);
       use_eq = (uu___112_1481.use_eq);
       is_iface = (uu___112_1481.is_iface);
       admit = (uu___112_1481.admit);
       lax = (uu___112_1481.lax);
       lax_universes = (uu___112_1481.lax_universes);
       type_of = (uu___112_1481.type_of);
       universe_of = (uu___112_1481.universe_of);
       use_bv_sorts = (uu___112_1481.use_bv_sorts);
       qname_and_index = (uu___112_1481.qname_and_index);
       proof_ns = (uu___112_1481.proof_ns);
       synth = (uu___112_1481.synth)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1489  ->
    let uu____1490 = FStar_ST.read stack in
    match uu____1490 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1502 -> failwith "Impossible: Too many pops"
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
    (let uu____1541 = pop_stack () in ());
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
        let uu____1562 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1574  ->
                  match uu____1574 with
                  | (m,uu____1578) -> FStar_Ident.lid_equals l m)) in
        (match uu____1562 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1583 = env in
               {
                 solver = (uu___113_1583.solver);
                 range = (uu___113_1583.range);
                 curmodule = (uu___113_1583.curmodule);
                 gamma = (uu___113_1583.gamma);
                 gamma_cache = (uu___113_1583.gamma_cache);
                 modules = (uu___113_1583.modules);
                 expected_typ = (uu___113_1583.expected_typ);
                 sigtab = (uu___113_1583.sigtab);
                 is_pattern = (uu___113_1583.is_pattern);
                 instantiate_imp = (uu___113_1583.instantiate_imp);
                 effects = (uu___113_1583.effects);
                 generalize = (uu___113_1583.generalize);
                 letrecs = (uu___113_1583.letrecs);
                 top_level = (uu___113_1583.top_level);
                 check_uvars = (uu___113_1583.check_uvars);
                 use_eq = (uu___113_1583.use_eq);
                 is_iface = (uu___113_1583.is_iface);
                 admit = (uu___113_1583.admit);
                 lax = (uu___113_1583.lax);
                 lax_universes = (uu___113_1583.lax_universes);
                 type_of = (uu___113_1583.type_of);
                 universe_of = (uu___113_1583.universe_of);
                 use_bv_sorts = (uu___113_1583.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_1583.proof_ns);
                 synth = (uu___113_1583.synth)
               }))
         | Some (uu____1586,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1592 = env in
               {
                 solver = (uu___114_1592.solver);
                 range = (uu___114_1592.range);
                 curmodule = (uu___114_1592.curmodule);
                 gamma = (uu___114_1592.gamma);
                 gamma_cache = (uu___114_1592.gamma_cache);
                 modules = (uu___114_1592.modules);
                 expected_typ = (uu___114_1592.expected_typ);
                 sigtab = (uu___114_1592.sigtab);
                 is_pattern = (uu___114_1592.is_pattern);
                 instantiate_imp = (uu___114_1592.instantiate_imp);
                 effects = (uu___114_1592.effects);
                 generalize = (uu___114_1592.generalize);
                 letrecs = (uu___114_1592.letrecs);
                 top_level = (uu___114_1592.top_level);
                 check_uvars = (uu___114_1592.check_uvars);
                 use_eq = (uu___114_1592.use_eq);
                 is_iface = (uu___114_1592.is_iface);
                 admit = (uu___114_1592.admit);
                 lax = (uu___114_1592.lax);
                 lax_universes = (uu___114_1592.lax_universes);
                 type_of = (uu___114_1592.type_of);
                 universe_of = (uu___114_1592.universe_of);
                 use_bv_sorts = (uu___114_1592.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_1592.proof_ns);
                 synth = (uu___114_1592.synth)
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
        (let uu___115_1612 = e in
         {
           solver = (uu___115_1612.solver);
           range = r;
           curmodule = (uu___115_1612.curmodule);
           gamma = (uu___115_1612.gamma);
           gamma_cache = (uu___115_1612.gamma_cache);
           modules = (uu___115_1612.modules);
           expected_typ = (uu___115_1612.expected_typ);
           sigtab = (uu___115_1612.sigtab);
           is_pattern = (uu___115_1612.is_pattern);
           instantiate_imp = (uu___115_1612.instantiate_imp);
           effects = (uu___115_1612.effects);
           generalize = (uu___115_1612.generalize);
           letrecs = (uu___115_1612.letrecs);
           top_level = (uu___115_1612.top_level);
           check_uvars = (uu___115_1612.check_uvars);
           use_eq = (uu___115_1612.use_eq);
           is_iface = (uu___115_1612.is_iface);
           admit = (uu___115_1612.admit);
           lax = (uu___115_1612.lax);
           lax_universes = (uu___115_1612.lax_universes);
           type_of = (uu___115_1612.type_of);
           universe_of = (uu___115_1612.universe_of);
           use_bv_sorts = (uu___115_1612.use_bv_sorts);
           qname_and_index = (uu___115_1612.qname_and_index);
           proof_ns = (uu___115_1612.proof_ns);
           synth = (uu___115_1612.synth)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1634 = env in
      {
        solver = (uu___116_1634.solver);
        range = (uu___116_1634.range);
        curmodule = lid;
        gamma = (uu___116_1634.gamma);
        gamma_cache = (uu___116_1634.gamma_cache);
        modules = (uu___116_1634.modules);
        expected_typ = (uu___116_1634.expected_typ);
        sigtab = (uu___116_1634.sigtab);
        is_pattern = (uu___116_1634.is_pattern);
        instantiate_imp = (uu___116_1634.instantiate_imp);
        effects = (uu___116_1634.effects);
        generalize = (uu___116_1634.generalize);
        letrecs = (uu___116_1634.letrecs);
        top_level = (uu___116_1634.top_level);
        check_uvars = (uu___116_1634.check_uvars);
        use_eq = (uu___116_1634.use_eq);
        is_iface = (uu___116_1634.is_iface);
        admit = (uu___116_1634.admit);
        lax = (uu___116_1634.lax);
        lax_universes = (uu___116_1634.lax_universes);
        type_of = (uu___116_1634.type_of);
        universe_of = (uu___116_1634.universe_of);
        use_bv_sorts = (uu___116_1634.use_bv_sorts);
        qname_and_index = (uu___116_1634.qname_and_index);
        proof_ns = (uu___116_1634.proof_ns);
        synth = (uu___116_1634.synth)
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
    let uu____1662 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1662
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1666  ->
    let uu____1667 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1667
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1691) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1710 = FStar_Syntax_Subst.subst vs t in (us, uu____1710)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1716  ->
    match uu___100_1716 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1730  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1742 = inst_tscheme t in
      match uu____1742 with
      | (us,t1) ->
          let uu____1749 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1749)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1765  ->
          match uu____1765 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1783 =
                         let uu____1784 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1789 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1794 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1795 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1784 uu____1789 uu____1794 uu____1795 in
                       failwith uu____1783)
                    else ();
                    (let uu____1797 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1797))
               | uu____1801 ->
                   let uu____1802 =
                     let uu____1803 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1803 in
                   failwith uu____1802)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1808 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1813 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1818 -> false
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
             | ([],uu____1846) -> Maybe
             | (uu____1850,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1862 -> No in
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
          let uu____1924 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1924 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1945  ->
                   match uu___101_1945 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1968 =
                           let uu____1978 =
                             let uu____1986 = inst_tscheme t in
                             FStar_Util.Inl uu____1986 in
                           (uu____1978, (FStar_Ident.range_of_lid l)) in
                         Some uu____1968
                       else None
                   | Binding_sig
                       (uu____2020,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____2022);
                                     FStar_Syntax_Syntax.sigrng = uu____2023;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____2024;
                                     FStar_Syntax_Syntax.sigmeta = uu____2025;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____2034 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____2034
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____2061 ->
                             Some t
                         | uu____2065 -> cache t in
                       let uu____2066 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____2066 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____2106 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____2106 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____2150 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2192 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____2192
         then
           let uu____2203 = find_in_sigtab env lid in
           match uu____2203 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2269) ->
          add_sigelts env ses
      | uu____2274 ->
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
            | uu____2283 -> ()))
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
        (fun uu___102_2303  ->
           match uu___102_2303 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2316 -> None)
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
          ((uu____2339,lb::[]),uu____2341,uu____2342) ->
          let uu____2351 =
            let uu____2356 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2362 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2356, uu____2362) in
          Some uu____2351
      | FStar_Syntax_Syntax.Sig_let ((uu____2369,lbs),uu____2371,uu____2372)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2392 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2399 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2399
                   then
                     let uu____2405 =
                       let uu____2410 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2416 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2410, uu____2416) in
                     Some uu____2405
                   else None)
      | uu____2428 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2448 =
          let uu____2453 =
            let uu____2456 =
              let uu____2457 =
                let uu____2460 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2460 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2457) in
            inst_tscheme uu____2456 in
          (uu____2453, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2448
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2474,uu____2475) ->
        let uu____2478 =
          let uu____2483 =
            let uu____2486 =
              let uu____2487 =
                let uu____2490 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2490 in
              (us, uu____2487) in
            inst_tscheme uu____2486 in
          (uu____2483, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2478
    | uu____2501 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2538 =
        match uu____2538 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2588,uvs,t,uu____2591,uu____2592,uu____2593);
                    FStar_Syntax_Syntax.sigrng = uu____2594;
                    FStar_Syntax_Syntax.sigquals = uu____2595;
                    FStar_Syntax_Syntax.sigmeta = uu____2596;_},None
                  )
                 ->
                 let uu____2606 =
                   let uu____2611 = inst_tscheme (uvs, t) in
                   (uu____2611, rng) in
                 Some uu____2606
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2623;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2625;_},None
                  )
                 ->
                 let uu____2633 =
                   let uu____2634 = in_cur_mod env l in uu____2634 = Yes in
                 if uu____2633
                 then
                   let uu____2640 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2640
                    then
                      let uu____2647 =
                        let uu____2652 = inst_tscheme (uvs, t) in
                        (uu____2652, rng) in
                      Some uu____2647
                    else None)
                 else
                   (let uu____2667 =
                      let uu____2672 = inst_tscheme (uvs, t) in
                      (uu____2672, rng) in
                    Some uu____2667)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2685,uu____2686);
                    FStar_Syntax_Syntax.sigrng = uu____2687;
                    FStar_Syntax_Syntax.sigquals = uu____2688;
                    FStar_Syntax_Syntax.sigmeta = uu____2689;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2708 =
                        let uu____2713 = inst_tscheme (uvs, k) in
                        (uu____2713, rng) in
                      Some uu____2708
                  | uu____2722 ->
                      let uu____2723 =
                        let uu____2728 =
                          let uu____2731 =
                            let uu____2732 =
                              let uu____2735 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2735 in
                            (uvs, uu____2732) in
                          inst_tscheme uu____2731 in
                        (uu____2728, rng) in
                      Some uu____2723)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2750,uu____2751);
                    FStar_Syntax_Syntax.sigrng = uu____2752;
                    FStar_Syntax_Syntax.sigquals = uu____2753;
                    FStar_Syntax_Syntax.sigmeta = uu____2754;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2774 =
                        let uu____2779 = inst_tscheme_with (uvs, k) us in
                        (uu____2779, rng) in
                      Some uu____2774
                  | uu____2788 ->
                      let uu____2789 =
                        let uu____2794 =
                          let uu____2797 =
                            let uu____2798 =
                              let uu____2801 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2801 in
                            (uvs, uu____2798) in
                          inst_tscheme_with uu____2797 us in
                        (uu____2794, rng) in
                      Some uu____2789)
             | FStar_Util.Inr se ->
                 let uu____2821 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2832;
                        FStar_Syntax_Syntax.sigrng = uu____2833;
                        FStar_Syntax_Syntax.sigquals = uu____2834;
                        FStar_Syntax_Syntax.sigmeta = uu____2835;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2844 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2821
                   (FStar_Util.map_option
                      (fun uu____2867  ->
                         match uu____2867 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2884 =
        let uu____2890 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2890 mapper in
      match uu____2884 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2942 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2942.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2942.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2942.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2965 = lookup_qname env l in
      match uu____2965 with | None  -> false | Some uu____2985 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____3015 = try_lookup_bv env bv in
      match uu____3015 with
      | None  ->
          let uu____3023 =
            let uu____3024 =
              let uu____3027 = variable_not_found bv in (uu____3027, bvr) in
            FStar_Errors.Error uu____3024 in
          raise uu____3023
      | Some (t,r) ->
          let uu____3034 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____3035 = FStar_Range.set_use_range r bvr in
          (uu____3034, uu____3035)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____3049 = try_lookup_lid_aux env l in
      match uu____3049 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____3091 =
            let uu____3096 =
              let uu____3099 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____3099) in
            (uu____3096, r1) in
          Some uu____3091
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____3118 = try_lookup_lid env l in
      match uu____3118 with
      | None  ->
          let uu____3132 =
            let uu____3133 =
              let uu____3136 = name_not_found l in
              (uu____3136, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____3133 in
          raise uu____3132
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_3159  ->
              match uu___103_3159 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____3161 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____3174 = lookup_qname env lid in
      match uu____3174 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3189,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3192;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3194;_},None
            ),uu____3195)
          ->
          let uu____3219 =
            let uu____3225 =
              let uu____3228 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____3228) in
            (uu____3225, q) in
          Some uu____3219
      | uu____3237 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3261 = lookup_qname env lid in
      match uu____3261 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3274,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3277;
              FStar_Syntax_Syntax.sigquals = uu____3278;
              FStar_Syntax_Syntax.sigmeta = uu____3279;_},None
            ),uu____3280)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3304 ->
          let uu____3315 =
            let uu____3316 =
              let uu____3319 = name_not_found lid in
              (uu____3319, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3316 in
          raise uu____3315
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3332 = lookup_qname env lid in
      match uu____3332 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3345,uvs,t,uu____3348,uu____3349,uu____3350);
              FStar_Syntax_Syntax.sigrng = uu____3351;
              FStar_Syntax_Syntax.sigquals = uu____3352;
              FStar_Syntax_Syntax.sigmeta = uu____3353;_},None
            ),uu____3354)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3380 ->
          let uu____3391 =
            let uu____3392 =
              let uu____3395 = name_not_found lid in
              (uu____3395, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3392 in
          raise uu____3391
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3409 = lookup_qname env lid in
      match uu____3409 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3423,uu____3424,uu____3425,uu____3426,uu____3427,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3429;
              FStar_Syntax_Syntax.sigquals = uu____3430;
              FStar_Syntax_Syntax.sigmeta = uu____3431;_},uu____3432),uu____3433)
          -> (true, dcs)
      | uu____3463 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3483 = lookup_qname env lid in
      match uu____3483 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3494,uu____3495,uu____3496,l,uu____3498,uu____3499);
              FStar_Syntax_Syntax.sigrng = uu____3500;
              FStar_Syntax_Syntax.sigquals = uu____3501;
              FStar_Syntax_Syntax.sigmeta = uu____3502;_},uu____3503),uu____3504)
          -> l
      | uu____3531 ->
          let uu____3542 =
            let uu____3543 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3543 in
          failwith uu____3542
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
        let uu____3570 = lookup_qname env lid in
        match uu____3570 with
        | Some (FStar_Util.Inr (se,None ),uu____3585) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3611,lbs),uu____3613,uu____3614) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3631 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3631
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3652 -> None)
        | uu____3655 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3678 = lookup_qname env ftv in
      match uu____3678 with
      | Some (FStar_Util.Inr (se,None ),uu____3691) ->
          let uu____3714 = effect_signature se in
          (match uu____3714 with
           | None  -> None
           | Some ((uu____3725,t),r) ->
               let uu____3734 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3734)
      | uu____3735 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3754 = try_lookup_effect_lid env ftv in
      match uu____3754 with
      | None  ->
          let uu____3756 =
            let uu____3757 =
              let uu____3760 = name_not_found ftv in
              (uu____3760, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3757 in
          raise uu____3756
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
        let uu____3777 = lookup_qname env lid0 in
        match uu____3777 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3795);
                FStar_Syntax_Syntax.sigrng = uu____3796;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3798;_},None
              ),uu____3799)
            ->
            let lid1 =
              let uu____3826 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3826 in
            let uu____3827 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3829  ->
                      match uu___104_3829 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3830 -> false)) in
            if uu____3827
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3847 =
                      let uu____3848 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3849 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3848 uu____3849 in
                    failwith uu____3847) in
               match (binders, univs1) with
               | ([],uu____3857) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3866,uu____3867::uu____3868::uu____3869) ->
                   let uu____3872 =
                     let uu____3873 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3874 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3873 uu____3874 in
                   failwith uu____3872
               | uu____3882 ->
                   let uu____3885 =
                     let uu____3888 =
                       let uu____3889 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3889) in
                     inst_tscheme_with uu____3888 insts in
                   (match uu____3885 with
                    | (uu____3897,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3900 =
                          let uu____3901 = FStar_Syntax_Subst.compress t1 in
                          uu____3901.FStar_Syntax_Syntax.n in
                        (match uu____3900 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3931 -> failwith "Impossible")))
        | uu____3935 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3963 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3963 with
        | None  -> None
        | Some (uu____3970,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3975 = find1 l2 in
            (match uu____3975 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3980 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3980 with
        | Some l1 -> l1
        | None  ->
            let uu____3983 = find1 l in
            (match uu____3983 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3997 = lookup_qname env l1 in
      match uu____3997 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____4009;
              FStar_Syntax_Syntax.sigrng = uu____4010;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____4012;_},uu____4013),uu____4014)
          -> q
      | uu____4039 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____4065 =
          let uu____4066 =
            let uu____4067 = FStar_Util.string_of_int i in
            let uu____4068 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____4067 uu____4068 in
          failwith uu____4066 in
        let uu____4069 = lookup_datacon env lid in
        match uu____4069 with
        | (uu____4072,t) ->
            let uu____4074 =
              let uu____4075 = FStar_Syntax_Subst.compress t in
              uu____4075.FStar_Syntax_Syntax.n in
            (match uu____4074 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4079) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____4102 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____4102 FStar_Pervasives.fst)
             | uu____4107 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____4116 = lookup_qname env l in
      match uu____4116 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____4127,uu____4128,uu____4129);
              FStar_Syntax_Syntax.sigrng = uu____4130;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4132;_},uu____4133),uu____4134)
          ->
          FStar_Util.for_some
            (fun uu___105_4159  ->
               match uu___105_4159 with
               | FStar_Syntax_Syntax.Projector uu____4160 -> true
               | uu____4163 -> false) quals
      | uu____4164 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4183 = lookup_qname env lid in
      match uu____4183 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____4194,uu____4195,uu____4196,uu____4197,uu____4198,uu____4199);
              FStar_Syntax_Syntax.sigrng = uu____4200;
              FStar_Syntax_Syntax.sigquals = uu____4201;
              FStar_Syntax_Syntax.sigmeta = uu____4202;_},uu____4203),uu____4204)
          -> true
      | uu____4231 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4250 = lookup_qname env lid in
      match uu____4250 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4261,uu____4262,uu____4263,uu____4264,uu____4265,uu____4266);
              FStar_Syntax_Syntax.sigrng = uu____4267;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4269;_},uu____4270),uu____4271)
          ->
          FStar_Util.for_some
            (fun uu___106_4300  ->
               match uu___106_4300 with
               | FStar_Syntax_Syntax.RecordType uu____4301 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4306 -> true
               | uu____4311 -> false) quals
      | uu____4312 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4331 = lookup_qname env lid in
      match uu____4331 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4342,uu____4343,uu____4344);
              FStar_Syntax_Syntax.sigrng = uu____4345;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4347;_},uu____4348),uu____4349)
          ->
          FStar_Util.for_some
            (fun uu___107_4378  ->
               match uu___107_4378 with
               | FStar_Syntax_Syntax.Action uu____4379 -> true
               | uu____4380 -> false) quals
      | uu____4381 -> false
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
      let uu____4402 =
        let uu____4403 = FStar_Syntax_Util.un_uinst head1 in
        uu____4403.FStar_Syntax_Syntax.n in
      match uu____4402 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4407 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4447 -> Some false
        | FStar_Util.Inr (se,uu____4456) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4465 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4469 -> Some true
             | uu____4478 -> Some false) in
      let uu____4479 =
        let uu____4481 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4481 mapper in
      match uu____4479 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4510 = lookup_qname env lid in
      match uu____4510 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4521,uu____4522,tps,uu____4524,uu____4525,uu____4526);
              FStar_Syntax_Syntax.sigrng = uu____4527;
              FStar_Syntax_Syntax.sigquals = uu____4528;
              FStar_Syntax_Syntax.sigmeta = uu____4529;_},uu____4530),uu____4531)
          -> FStar_List.length tps
      | uu____4564 ->
          let uu____4575 =
            let uu____4576 =
              let uu____4579 = name_not_found lid in
              (uu____4579, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4576 in
          raise uu____4575
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
           (fun uu____4603  ->
              match uu____4603 with
              | (d,uu____4608) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4619 = effect_decl_opt env l in
      match uu____4619 with
      | None  ->
          let uu____4627 =
            let uu____4628 =
              let uu____4631 = name_not_found l in
              (uu____4631, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4628 in
          raise uu____4627
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
            (let uu____4677 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4701  ->
                       match uu____4701 with
                       | (m1,m2,uu____4709,uu____4710,uu____4711) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4677 with
             | None  ->
                 let uu____4720 =
                   let uu____4721 =
                     let uu____4724 =
                       let uu____4725 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4726 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4725
                         uu____4726 in
                     (uu____4724, (env.range)) in
                   FStar_Errors.Error uu____4721 in
                 raise uu____4720
             | Some (uu____4730,uu____4731,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4784 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4796  ->
            match uu____4796 with
            | (d,uu____4800) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4784 with
  | None  ->
      let uu____4807 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4807
  | Some (md,_q) ->
      let uu____4816 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4816 with
       | (uu____4823,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4831)::(wp,uu____4833)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4855 -> failwith "Impossible"))
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
                 let uu____4897 = get_range env in
                 let uu____4898 =
                   let uu____4901 =
                     let uu____4902 =
                       let uu____4912 =
                         let uu____4914 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4914] in
                       (null_wp, uu____4912) in
                     FStar_Syntax_Syntax.Tm_app uu____4902 in
                   FStar_Syntax_Syntax.mk uu____4901 in
                 uu____4898 None uu____4897 in
               let uu____4924 =
                 let uu____4925 =
                   let uu____4931 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4931] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4925;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4924)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4942 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4942.order);
              joins = (uu___118_4942.joins)
            } in
          let uu___119_4947 = env in
          {
            solver = (uu___119_4947.solver);
            range = (uu___119_4947.range);
            curmodule = (uu___119_4947.curmodule);
            gamma = (uu___119_4947.gamma);
            gamma_cache = (uu___119_4947.gamma_cache);
            modules = (uu___119_4947.modules);
            expected_typ = (uu___119_4947.expected_typ);
            sigtab = (uu___119_4947.sigtab);
            is_pattern = (uu___119_4947.is_pattern);
            instantiate_imp = (uu___119_4947.instantiate_imp);
            effects;
            generalize = (uu___119_4947.generalize);
            letrecs = (uu___119_4947.letrecs);
            top_level = (uu___119_4947.top_level);
            check_uvars = (uu___119_4947.check_uvars);
            use_eq = (uu___119_4947.use_eq);
            is_iface = (uu___119_4947.is_iface);
            admit = (uu___119_4947.admit);
            lax = (uu___119_4947.lax);
            lax_universes = (uu___119_4947.lax_universes);
            type_of = (uu___119_4947.type_of);
            universe_of = (uu___119_4947.universe_of);
            use_bv_sorts = (uu___119_4947.use_bv_sorts);
            qname_and_index = (uu___119_4947.qname_and_index);
            proof_ns = (uu___119_4947.proof_ns);
            synth = (uu___119_4947.synth)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4964 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4964 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____5043 = (e1.mlift).mlift_wp t wp in
                              let uu____5044 = l1 t wp e in
                              l2 t uu____5043 uu____5044))
                | uu____5045 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____5080 = inst_tscheme lift_t in
            match uu____5080 with
            | (uu____5085,lift_t1) ->
                let uu____5087 =
                  let uu____5090 =
                    let uu____5091 =
                      let uu____5101 =
                        let uu____5103 = FStar_Syntax_Syntax.as_arg r in
                        let uu____5104 =
                          let uu____5106 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____5106] in
                        uu____5103 :: uu____5104 in
                      (lift_t1, uu____5101) in
                    FStar_Syntax_Syntax.Tm_app uu____5091 in
                  FStar_Syntax_Syntax.mk uu____5090 in
                uu____5087 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____5151 = inst_tscheme lift_t in
            match uu____5151 with
            | (uu____5156,lift_t1) ->
                let uu____5158 =
                  let uu____5161 =
                    let uu____5162 =
                      let uu____5172 =
                        let uu____5174 = FStar_Syntax_Syntax.as_arg r in
                        let uu____5175 =
                          let uu____5177 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____5178 =
                            let uu____5180 = FStar_Syntax_Syntax.as_arg e in
                            [uu____5180] in
                          uu____5177 :: uu____5178 in
                        uu____5174 :: uu____5175 in
                      (lift_t1, uu____5172) in
                    FStar_Syntax_Syntax.Tm_app uu____5162 in
                  FStar_Syntax_Syntax.mk uu____5161 in
                uu____5158 None e.FStar_Syntax_Syntax.pos in
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
              let uu____5221 =
                let uu____5222 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____5222
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____5221 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____5226 =
              let uu____5227 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____5227 in
            let uu____5228 =
              let uu____5229 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____5244 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____5244) in
              FStar_Util.dflt "none" uu____5229 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____5226
              uu____5228 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____5257  ->
                    match uu____5257 with
                    | (e,uu____5262) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____5275 =
            match uu____5275 with
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
              let uu____5300 =
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
                                    (let uu____5312 =
                                       let uu____5317 =
                                         find_edge order1 (i, k) in
                                       let uu____5319 =
                                         find_edge order1 (k, j) in
                                       (uu____5317, uu____5319) in
                                     match uu____5312 with
                                     | (Some e1,Some e2) ->
                                         let uu____5328 = compose_edges e1 e2 in
                                         [uu____5328]
                                     | uu____5329 -> []))))) in
              FStar_List.append order1 uu____5300 in
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
                   let uu____5344 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5345 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5345
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5344
                   then
                     let uu____5348 =
                       let uu____5349 =
                         let uu____5352 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5353 = get_range env in
                         (uu____5352, uu____5353) in
                       FStar_Errors.Error uu____5349 in
                     raise uu____5348
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
                                            let uu____5416 =
                                              let uu____5421 =
                                                find_edge order2 (i, k) in
                                              let uu____5423 =
                                                find_edge order2 (j, k) in
                                              (uu____5421, uu____5423) in
                                            match uu____5416 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5446,uu____5447)
                                                     ->
                                                     let uu____5451 =
                                                       let uu____5454 =
                                                         let uu____5455 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5455 in
                                                       let uu____5457 =
                                                         let uu____5458 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5458 in
                                                       (uu____5454,
                                                         uu____5457) in
                                                     (match uu____5451 with
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
                                            | uu____5477 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5516 = env.effects in
              { decls = (uu___120_5516.decls); order = order2; joins } in
            let uu___121_5517 = env in
            {
              solver = (uu___121_5517.solver);
              range = (uu___121_5517.range);
              curmodule = (uu___121_5517.curmodule);
              gamma = (uu___121_5517.gamma);
              gamma_cache = (uu___121_5517.gamma_cache);
              modules = (uu___121_5517.modules);
              expected_typ = (uu___121_5517.expected_typ);
              sigtab = (uu___121_5517.sigtab);
              is_pattern = (uu___121_5517.is_pattern);
              instantiate_imp = (uu___121_5517.instantiate_imp);
              effects;
              generalize = (uu___121_5517.generalize);
              letrecs = (uu___121_5517.letrecs);
              top_level = (uu___121_5517.top_level);
              check_uvars = (uu___121_5517.check_uvars);
              use_eq = (uu___121_5517.use_eq);
              is_iface = (uu___121_5517.is_iface);
              admit = (uu___121_5517.admit);
              lax = (uu___121_5517.lax);
              lax_universes = (uu___121_5517.lax_universes);
              type_of = (uu___121_5517.type_of);
              universe_of = (uu___121_5517.universe_of);
              use_bv_sorts = (uu___121_5517.use_bv_sorts);
              qname_and_index = (uu___121_5517.qname_and_index);
              proof_ns = (uu___121_5517.proof_ns);
              synth = (uu___121_5517.synth)
            }))
      | uu____5518 -> env
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
        | uu____5542 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5552 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5552 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5562 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5562 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5584 =
                     let uu____5585 =
                       let uu____5588 =
                         let uu____5589 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5598 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5609 =
                           let uu____5610 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5610 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5589 uu____5598 uu____5609 in
                       (uu____5588, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5585 in
                   raise uu____5584)
                else ();
                (let inst1 =
                   let uu____5614 =
                     let uu____5620 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5620 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5627  ->
                        fun uu____5628  ->
                          match (uu____5627, uu____5628) with
                          | ((x,uu____5642),(t,uu____5644)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5614 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5659 =
                     let uu___122_5660 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5660.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5660.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5660.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5660.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5659
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5695 =
    let uu____5700 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5700 in
  match uu____5695 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5716 =
        only_reifiable &&
          (let uu____5717 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5717) in
      if uu____5716
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5730 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5732 =
               let uu____5741 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5741) in
             (match uu____5732 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5775 =
                    let uu____5778 = get_range env in
                    let uu____5779 =
                      let uu____5782 =
                        let uu____5783 =
                          let uu____5793 =
                            let uu____5795 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5795; wp] in
                          (repr, uu____5793) in
                        FStar_Syntax_Syntax.Tm_app uu____5783 in
                      FStar_Syntax_Syntax.mk uu____5782 in
                    uu____5779 None uu____5778 in
                  Some uu____5775))
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
          let uu____5845 =
            let uu____5846 =
              let uu____5849 =
                let uu____5850 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5850 in
              let uu____5851 = get_range env in (uu____5849, uu____5851) in
            FStar_Errors.Error uu____5846 in
          raise uu____5845 in
        let uu____5852 = effect_repr_aux true env c u_c in
        match uu____5852 with
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
        | FStar_Util.Inr (eff_name,uu____5888) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5903 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5912 =
        let uu____5913 = FStar_Syntax_Subst.compress t in
        uu____5913.FStar_Syntax_Syntax.n in
      match uu____5912 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5916,c) ->
          is_reifiable_comp env c
      | uu____5928 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5948)::uu____5949 -> x :: rest
        | (Binding_sig_inst uu____5954)::uu____5955 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5964 = push1 x rest1 in local :: uu____5964 in
      let uu___123_5966 = env in
      let uu____5967 = push1 s env.gamma in
      {
        solver = (uu___123_5966.solver);
        range = (uu___123_5966.range);
        curmodule = (uu___123_5966.curmodule);
        gamma = uu____5967;
        gamma_cache = (uu___123_5966.gamma_cache);
        modules = (uu___123_5966.modules);
        expected_typ = (uu___123_5966.expected_typ);
        sigtab = (uu___123_5966.sigtab);
        is_pattern = (uu___123_5966.is_pattern);
        instantiate_imp = (uu___123_5966.instantiate_imp);
        effects = (uu___123_5966.effects);
        generalize = (uu___123_5966.generalize);
        letrecs = (uu___123_5966.letrecs);
        top_level = (uu___123_5966.top_level);
        check_uvars = (uu___123_5966.check_uvars);
        use_eq = (uu___123_5966.use_eq);
        is_iface = (uu___123_5966.is_iface);
        admit = (uu___123_5966.admit);
        lax = (uu___123_5966.lax);
        lax_universes = (uu___123_5966.lax_universes);
        type_of = (uu___123_5966.type_of);
        universe_of = (uu___123_5966.universe_of);
        use_bv_sorts = (uu___123_5966.use_bv_sorts);
        qname_and_index = (uu___123_5966.qname_and_index);
        proof_ns = (uu___123_5966.proof_ns);
        synth = (uu___123_5966.synth)
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
      let uu___124_6001 = env in
      {
        solver = (uu___124_6001.solver);
        range = (uu___124_6001.range);
        curmodule = (uu___124_6001.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_6001.gamma_cache);
        modules = (uu___124_6001.modules);
        expected_typ = (uu___124_6001.expected_typ);
        sigtab = (uu___124_6001.sigtab);
        is_pattern = (uu___124_6001.is_pattern);
        instantiate_imp = (uu___124_6001.instantiate_imp);
        effects = (uu___124_6001.effects);
        generalize = (uu___124_6001.generalize);
        letrecs = (uu___124_6001.letrecs);
        top_level = (uu___124_6001.top_level);
        check_uvars = (uu___124_6001.check_uvars);
        use_eq = (uu___124_6001.use_eq);
        is_iface = (uu___124_6001.is_iface);
        admit = (uu___124_6001.admit);
        lax = (uu___124_6001.lax);
        lax_universes = (uu___124_6001.lax_universes);
        type_of = (uu___124_6001.type_of);
        universe_of = (uu___124_6001.universe_of);
        use_bv_sorts = (uu___124_6001.use_bv_sorts);
        qname_and_index = (uu___124_6001.qname_and_index);
        proof_ns = (uu___124_6001.proof_ns);
        synth = (uu___124_6001.synth)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_6025 = env in
             {
               solver = (uu___125_6025.solver);
               range = (uu___125_6025.range);
               curmodule = (uu___125_6025.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_6025.gamma_cache);
               modules = (uu___125_6025.modules);
               expected_typ = (uu___125_6025.expected_typ);
               sigtab = (uu___125_6025.sigtab);
               is_pattern = (uu___125_6025.is_pattern);
               instantiate_imp = (uu___125_6025.instantiate_imp);
               effects = (uu___125_6025.effects);
               generalize = (uu___125_6025.generalize);
               letrecs = (uu___125_6025.letrecs);
               top_level = (uu___125_6025.top_level);
               check_uvars = (uu___125_6025.check_uvars);
               use_eq = (uu___125_6025.use_eq);
               is_iface = (uu___125_6025.is_iface);
               admit = (uu___125_6025.admit);
               lax = (uu___125_6025.lax);
               lax_universes = (uu___125_6025.lax_universes);
               type_of = (uu___125_6025.type_of);
               universe_of = (uu___125_6025.universe_of);
               use_bv_sorts = (uu___125_6025.use_bv_sorts);
               qname_and_index = (uu___125_6025.qname_and_index);
               proof_ns = (uu___125_6025.proof_ns);
               synth = (uu___125_6025.synth)
             }))
    | uu____6026 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____6041  ->
             match uu____6041 with | (x,uu____6045) -> push_bv env1 x) env bs
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
            let uu___126_6067 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_6067.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_6067.FStar_Syntax_Syntax.index);
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
      (let uu___127_6102 = env in
       {
         solver = (uu___127_6102.solver);
         range = (uu___127_6102.range);
         curmodule = (uu___127_6102.curmodule);
         gamma = [];
         gamma_cache = (uu___127_6102.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_6102.sigtab);
         is_pattern = (uu___127_6102.is_pattern);
         instantiate_imp = (uu___127_6102.instantiate_imp);
         effects = (uu___127_6102.effects);
         generalize = (uu___127_6102.generalize);
         letrecs = (uu___127_6102.letrecs);
         top_level = (uu___127_6102.top_level);
         check_uvars = (uu___127_6102.check_uvars);
         use_eq = (uu___127_6102.use_eq);
         is_iface = (uu___127_6102.is_iface);
         admit = (uu___127_6102.admit);
         lax = (uu___127_6102.lax);
         lax_universes = (uu___127_6102.lax_universes);
         type_of = (uu___127_6102.type_of);
         universe_of = (uu___127_6102.universe_of);
         use_bv_sorts = (uu___127_6102.use_bv_sorts);
         qname_and_index = (uu___127_6102.qname_and_index);
         proof_ns = (uu___127_6102.proof_ns);
         synth = (uu___127_6102.synth)
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
        let uu____6131 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____6131 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____6147 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____6147)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_6159 = env in
      {
        solver = (uu___128_6159.solver);
        range = (uu___128_6159.range);
        curmodule = (uu___128_6159.curmodule);
        gamma = (uu___128_6159.gamma);
        gamma_cache = (uu___128_6159.gamma_cache);
        modules = (uu___128_6159.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_6159.sigtab);
        is_pattern = (uu___128_6159.is_pattern);
        instantiate_imp = (uu___128_6159.instantiate_imp);
        effects = (uu___128_6159.effects);
        generalize = (uu___128_6159.generalize);
        letrecs = (uu___128_6159.letrecs);
        top_level = (uu___128_6159.top_level);
        check_uvars = (uu___128_6159.check_uvars);
        use_eq = false;
        is_iface = (uu___128_6159.is_iface);
        admit = (uu___128_6159.admit);
        lax = (uu___128_6159.lax);
        lax_universes = (uu___128_6159.lax_universes);
        type_of = (uu___128_6159.type_of);
        universe_of = (uu___128_6159.universe_of);
        use_bv_sorts = (uu___128_6159.use_bv_sorts);
        qname_and_index = (uu___128_6159.qname_and_index);
        proof_ns = (uu___128_6159.proof_ns);
        synth = (uu___128_6159.synth)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____6177 = expected_typ env_ in
    ((let uu___129_6180 = env_ in
      {
        solver = (uu___129_6180.solver);
        range = (uu___129_6180.range);
        curmodule = (uu___129_6180.curmodule);
        gamma = (uu___129_6180.gamma);
        gamma_cache = (uu___129_6180.gamma_cache);
        modules = (uu___129_6180.modules);
        expected_typ = None;
        sigtab = (uu___129_6180.sigtab);
        is_pattern = (uu___129_6180.is_pattern);
        instantiate_imp = (uu___129_6180.instantiate_imp);
        effects = (uu___129_6180.effects);
        generalize = (uu___129_6180.generalize);
        letrecs = (uu___129_6180.letrecs);
        top_level = (uu___129_6180.top_level);
        check_uvars = (uu___129_6180.check_uvars);
        use_eq = false;
        is_iface = (uu___129_6180.is_iface);
        admit = (uu___129_6180.admit);
        lax = (uu___129_6180.lax);
        lax_universes = (uu___129_6180.lax_universes);
        type_of = (uu___129_6180.type_of);
        universe_of = (uu___129_6180.universe_of);
        use_bv_sorts = (uu___129_6180.use_bv_sorts);
        qname_and_index = (uu___129_6180.qname_and_index);
        proof_ns = (uu___129_6180.proof_ns);
        synth = (uu___129_6180.synth)
      }), uu____6177)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____6193 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_6197  ->
                    match uu___108_6197 with
                    | Binding_sig (uu____6199,se) -> [se]
                    | uu____6203 -> [])) in
          FStar_All.pipe_right uu____6193 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_6208 = env in
       {
         solver = (uu___130_6208.solver);
         range = (uu___130_6208.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_6208.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_6208.expected_typ);
         sigtab = (uu___130_6208.sigtab);
         is_pattern = (uu___130_6208.is_pattern);
         instantiate_imp = (uu___130_6208.instantiate_imp);
         effects = (uu___130_6208.effects);
         generalize = (uu___130_6208.generalize);
         letrecs = (uu___130_6208.letrecs);
         top_level = (uu___130_6208.top_level);
         check_uvars = (uu___130_6208.check_uvars);
         use_eq = (uu___130_6208.use_eq);
         is_iface = (uu___130_6208.is_iface);
         admit = (uu___130_6208.admit);
         lax = (uu___130_6208.lax);
         lax_universes = (uu___130_6208.lax_universes);
         type_of = (uu___130_6208.type_of);
         universe_of = (uu___130_6208.universe_of);
         use_bv_sorts = (uu___130_6208.use_bv_sorts);
         qname_and_index = (uu___130_6208.qname_and_index);
         proof_ns = (uu___130_6208.proof_ns);
         synth = (uu___130_6208.synth)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____6259)::tl1 -> aux out tl1
      | (Binding_lid (uu____6262,(uu____6263,t)))::tl1 ->
          let uu____6272 =
            let uu____6276 = FStar_Syntax_Free.uvars t in ext out uu____6276 in
          aux uu____6272 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6280;
            FStar_Syntax_Syntax.index = uu____6281;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6287 =
            let uu____6291 = FStar_Syntax_Free.uvars t in ext out uu____6291 in
          aux uu____6287 tl1
      | (Binding_sig uu____6295)::uu____6296 -> out
      | (Binding_sig_inst uu____6301)::uu____6302 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6340)::tl1 -> aux out tl1
      | (Binding_univ uu____6347)::tl1 -> aux out tl1
      | (Binding_lid (uu____6350,(uu____6351,t)))::tl1 ->
          let uu____6360 =
            let uu____6362 = FStar_Syntax_Free.univs t in ext out uu____6362 in
          aux uu____6360 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6364;
            FStar_Syntax_Syntax.index = uu____6365;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6371 =
            let uu____6373 = FStar_Syntax_Free.univs t in ext out uu____6373 in
          aux uu____6371 tl1
      | (Binding_sig uu____6375)::uu____6376 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6414)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6424 = FStar_Util.set_add uname out in aux uu____6424 tl1
      | (Binding_lid (uu____6426,(uu____6427,t)))::tl1 ->
          let uu____6436 =
            let uu____6438 = FStar_Syntax_Free.univnames t in
            ext out uu____6438 in
          aux uu____6436 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6440;
            FStar_Syntax_Syntax.index = uu____6441;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6447 =
            let uu____6449 = FStar_Syntax_Free.univnames t in
            ext out uu____6449 in
          aux uu____6447 tl1
      | (Binding_sig uu____6451)::uu____6452 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6469  ->
            match uu___109_6469 with
            | Binding_var x -> [x]
            | Binding_lid uu____6472 -> []
            | Binding_sig uu____6475 -> []
            | Binding_univ uu____6479 -> []
            | Binding_sig_inst uu____6480 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6491 =
      let uu____6493 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6493
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6491 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6512 =
      let uu____6513 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6517  ->
                match uu___110_6517 with
                | Binding_var x ->
                    let uu____6519 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6519
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6522) ->
                    let uu____6523 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6523
                | Binding_sig (ls,uu____6525) ->
                    let uu____6528 =
                      let uu____6529 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6529
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6528
                | Binding_sig_inst (ls,uu____6535,uu____6536) ->
                    let uu____6539 =
                      let uu____6540 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6540
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6539)) in
      FStar_All.pipe_right uu____6513 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6512 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6554 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6554
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6575  ->
                 fun uu____6576  ->
                   match (uu____6575, uu____6576) with
                   | ((b1,uu____6586),(b2,uu____6588)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6636  ->
             match uu___111_6636 with
             | Binding_sig (lids,uu____6640) -> FStar_List.append lids keys
             | uu____6643 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6645  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6672) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6684,uu____6685) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6709 = list_prefix p path1 in
            if uu____6709 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6721 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6721
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6744 = e in
            {
              solver = (uu___131_6744.solver);
              range = (uu___131_6744.range);
              curmodule = (uu___131_6744.curmodule);
              gamma = (uu___131_6744.gamma);
              gamma_cache = (uu___131_6744.gamma_cache);
              modules = (uu___131_6744.modules);
              expected_typ = (uu___131_6744.expected_typ);
              sigtab = (uu___131_6744.sigtab);
              is_pattern = (uu___131_6744.is_pattern);
              instantiate_imp = (uu___131_6744.instantiate_imp);
              effects = (uu___131_6744.effects);
              generalize = (uu___131_6744.generalize);
              letrecs = (uu___131_6744.letrecs);
              top_level = (uu___131_6744.top_level);
              check_uvars = (uu___131_6744.check_uvars);
              use_eq = (uu___131_6744.use_eq);
              is_iface = (uu___131_6744.is_iface);
              admit = (uu___131_6744.admit);
              lax = (uu___131_6744.lax);
              lax_universes = (uu___131_6744.lax_universes);
              type_of = (uu___131_6744.type_of);
              universe_of = (uu___131_6744.universe_of);
              use_bv_sorts = (uu___131_6744.use_bv_sorts);
              qname_and_index = (uu___131_6744.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_6744.synth)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6768 = e in
    {
      solver = (uu___132_6768.solver);
      range = (uu___132_6768.range);
      curmodule = (uu___132_6768.curmodule);
      gamma = (uu___132_6768.gamma);
      gamma_cache = (uu___132_6768.gamma_cache);
      modules = (uu___132_6768.modules);
      expected_typ = (uu___132_6768.expected_typ);
      sigtab = (uu___132_6768.sigtab);
      is_pattern = (uu___132_6768.is_pattern);
      instantiate_imp = (uu___132_6768.instantiate_imp);
      effects = (uu___132_6768.effects);
      generalize = (uu___132_6768.generalize);
      letrecs = (uu___132_6768.letrecs);
      top_level = (uu___132_6768.top_level);
      check_uvars = (uu___132_6768.check_uvars);
      use_eq = (uu___132_6768.use_eq);
      is_iface = (uu___132_6768.is_iface);
      admit = (uu___132_6768.admit);
      lax = (uu___132_6768.lax);
      lax_universes = (uu___132_6768.lax_universes);
      type_of = (uu___132_6768.type_of);
      universe_of = (uu___132_6768.universe_of);
      use_bv_sorts = (uu___132_6768.use_bv_sorts);
      qname_and_index = (uu___132_6768.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_6768.synth)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6778::rest ->
        let uu___133_6781 = e in
        {
          solver = (uu___133_6781.solver);
          range = (uu___133_6781.range);
          curmodule = (uu___133_6781.curmodule);
          gamma = (uu___133_6781.gamma);
          gamma_cache = (uu___133_6781.gamma_cache);
          modules = (uu___133_6781.modules);
          expected_typ = (uu___133_6781.expected_typ);
          sigtab = (uu___133_6781.sigtab);
          is_pattern = (uu___133_6781.is_pattern);
          instantiate_imp = (uu___133_6781.instantiate_imp);
          effects = (uu___133_6781.effects);
          generalize = (uu___133_6781.generalize);
          letrecs = (uu___133_6781.letrecs);
          top_level = (uu___133_6781.top_level);
          check_uvars = (uu___133_6781.check_uvars);
          use_eq = (uu___133_6781.use_eq);
          is_iface = (uu___133_6781.is_iface);
          admit = (uu___133_6781.admit);
          lax = (uu___133_6781.lax);
          lax_universes = (uu___133_6781.lax_universes);
          type_of = (uu___133_6781.type_of);
          universe_of = (uu___133_6781.universe_of);
          use_bv_sorts = (uu___133_6781.use_bv_sorts);
          qname_and_index = (uu___133_6781.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_6781.synth)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6794 = e in
      {
        solver = (uu___134_6794.solver);
        range = (uu___134_6794.range);
        curmodule = (uu___134_6794.curmodule);
        gamma = (uu___134_6794.gamma);
        gamma_cache = (uu___134_6794.gamma_cache);
        modules = (uu___134_6794.modules);
        expected_typ = (uu___134_6794.expected_typ);
        sigtab = (uu___134_6794.sigtab);
        is_pattern = (uu___134_6794.is_pattern);
        instantiate_imp = (uu___134_6794.instantiate_imp);
        effects = (uu___134_6794.effects);
        generalize = (uu___134_6794.generalize);
        letrecs = (uu___134_6794.letrecs);
        top_level = (uu___134_6794.top_level);
        check_uvars = (uu___134_6794.check_uvars);
        use_eq = (uu___134_6794.use_eq);
        is_iface = (uu___134_6794.is_iface);
        admit = (uu___134_6794.admit);
        lax = (uu___134_6794.lax);
        lax_universes = (uu___134_6794.lax_universes);
        type_of = (uu___134_6794.type_of);
        universe_of = (uu___134_6794.universe_of);
        use_bv_sorts = (uu___134_6794.use_bv_sorts);
        qname_and_index = (uu___134_6794.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_6794.synth)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6813 =
        FStar_List.map
          (fun fpns  ->
             let uu____6824 =
               let uu____6825 =
                 let uu____6826 =
                   FStar_List.map
                     (fun uu____6831  ->
                        match uu____6831 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6826 in
               Prims.strcat uu____6825 "]" in
             Prims.strcat "[" uu____6824) pns in
      FStar_String.concat ";" uu____6813 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6840  -> ());
    push = (fun uu____6841  -> ());
    pop = (fun uu____6842  -> ());
    mark = (fun uu____6843  -> ());
    reset_mark = (fun uu____6844  -> ());
    commit_mark = (fun uu____6845  -> ());
    encode_modul = (fun uu____6846  -> fun uu____6847  -> ());
    encode_sig = (fun uu____6848  -> fun uu____6849  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6856  -> fun uu____6857  -> fun uu____6858  -> ());
    is_trivial = (fun uu____6862  -> fun uu____6863  -> false);
    finish = (fun uu____6864  -> ());
    refresh = (fun uu____6865  -> ())
  }