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
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;
  is_native_tactic: FStar_Ident.lid -> Prims.bool;}
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
      | (NoDelta ,uu____994) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____995,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____996,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____997 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____1007 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____1015 =
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
          let uu____1054 = new_gamma_cache () in
          let uu____1056 = new_sigtab () in
          let uu____1058 =
            let uu____1059 = FStar_Options.using_facts_from () in
            match uu____1059 with
            | Some ns ->
                let uu____1065 =
                  let uu____1070 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____1070 [([], false)] in
                [uu____1065]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1054;
            modules = [];
            expected_typ = None;
            sigtab = uu____1056;
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
            proof_ns = uu____1058;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____1122  -> false)
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1152  ->
    let uu____1153 = FStar_ST.read query_indices in
    match uu____1153 with
    | [] -> failwith "Empty query indices!"
    | uu____1167 ->
        let uu____1172 =
          let uu____1177 =
            let uu____1181 = FStar_ST.read query_indices in
            FStar_List.hd uu____1181 in
          let uu____1195 = FStar_ST.read query_indices in uu____1177 ::
            uu____1195 in
        FStar_ST.write query_indices uu____1172
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1217  ->
    let uu____1218 = FStar_ST.read query_indices in
    match uu____1218 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1254  ->
    match uu____1254 with
    | (l,n1) ->
        let uu____1259 = FStar_ST.read query_indices in
        (match uu____1259 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1293 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1303  ->
    let uu____1304 = FStar_ST.read query_indices in FStar_List.hd uu____1304
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1320  ->
    let uu____1321 = FStar_ST.read query_indices in
    match uu____1321 with
    | hd1::uu____1333::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1360 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1374 =
       let uu____1376 = FStar_ST.read stack in env :: uu____1376 in
     FStar_ST.write stack uu____1374);
    (let uu___114_1384 = env in
     let uu____1385 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1387 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___114_1384.solver);
       range = (uu___114_1384.range);
       curmodule = (uu___114_1384.curmodule);
       gamma = (uu___114_1384.gamma);
       gamma_cache = uu____1385;
       modules = (uu___114_1384.modules);
       expected_typ = (uu___114_1384.expected_typ);
       sigtab = uu____1387;
       is_pattern = (uu___114_1384.is_pattern);
       instantiate_imp = (uu___114_1384.instantiate_imp);
       effects = (uu___114_1384.effects);
       generalize = (uu___114_1384.generalize);
       letrecs = (uu___114_1384.letrecs);
       top_level = (uu___114_1384.top_level);
       check_uvars = (uu___114_1384.check_uvars);
       use_eq = (uu___114_1384.use_eq);
       is_iface = (uu___114_1384.is_iface);
       admit = (uu___114_1384.admit);
       lax = (uu___114_1384.lax);
       lax_universes = (uu___114_1384.lax_universes);
       type_of = (uu___114_1384.type_of);
       universe_of = (uu___114_1384.universe_of);
       use_bv_sorts = (uu___114_1384.use_bv_sorts);
       qname_and_index = (uu___114_1384.qname_and_index);
       proof_ns = (uu___114_1384.proof_ns);
       synth = (uu___114_1384.synth);
       is_native_tactic = (uu___114_1384.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1391  ->
    let uu____1392 = FStar_ST.read stack in
    match uu____1392 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1404 -> failwith "Impossible: Too many pops"
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
    (let uu____1436 = pop_stack () in ());
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
        let uu____1455 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1467  ->
                  match uu____1467 with
                  | (m,uu____1471) -> FStar_Ident.lid_equals l m)) in
        (match uu____1455 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___115_1476 = env in
               {
                 solver = (uu___115_1476.solver);
                 range = (uu___115_1476.range);
                 curmodule = (uu___115_1476.curmodule);
                 gamma = (uu___115_1476.gamma);
                 gamma_cache = (uu___115_1476.gamma_cache);
                 modules = (uu___115_1476.modules);
                 expected_typ = (uu___115_1476.expected_typ);
                 sigtab = (uu___115_1476.sigtab);
                 is_pattern = (uu___115_1476.is_pattern);
                 instantiate_imp = (uu___115_1476.instantiate_imp);
                 effects = (uu___115_1476.effects);
                 generalize = (uu___115_1476.generalize);
                 letrecs = (uu___115_1476.letrecs);
                 top_level = (uu___115_1476.top_level);
                 check_uvars = (uu___115_1476.check_uvars);
                 use_eq = (uu___115_1476.use_eq);
                 is_iface = (uu___115_1476.is_iface);
                 admit = (uu___115_1476.admit);
                 lax = (uu___115_1476.lax);
                 lax_universes = (uu___115_1476.lax_universes);
                 type_of = (uu___115_1476.type_of);
                 universe_of = (uu___115_1476.universe_of);
                 use_bv_sorts = (uu___115_1476.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___115_1476.proof_ns);
                 synth = (uu___115_1476.synth);
                 is_native_tactic = (uu___115_1476.is_native_tactic)
               }))
         | Some (uu____1479,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_1485 = env in
               {
                 solver = (uu___116_1485.solver);
                 range = (uu___116_1485.range);
                 curmodule = (uu___116_1485.curmodule);
                 gamma = (uu___116_1485.gamma);
                 gamma_cache = (uu___116_1485.gamma_cache);
                 modules = (uu___116_1485.modules);
                 expected_typ = (uu___116_1485.expected_typ);
                 sigtab = (uu___116_1485.sigtab);
                 is_pattern = (uu___116_1485.is_pattern);
                 instantiate_imp = (uu___116_1485.instantiate_imp);
                 effects = (uu___116_1485.effects);
                 generalize = (uu___116_1485.generalize);
                 letrecs = (uu___116_1485.letrecs);
                 top_level = (uu___116_1485.top_level);
                 check_uvars = (uu___116_1485.check_uvars);
                 use_eq = (uu___116_1485.use_eq);
                 is_iface = (uu___116_1485.is_iface);
                 admit = (uu___116_1485.admit);
                 lax = (uu___116_1485.lax);
                 lax_universes = (uu___116_1485.lax_universes);
                 type_of = (uu___116_1485.type_of);
                 universe_of = (uu___116_1485.universe_of);
                 use_bv_sorts = (uu___116_1485.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___116_1485.proof_ns);
                 synth = (uu___116_1485.synth);
                 is_native_tactic = (uu___116_1485.is_native_tactic)
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
        (let uu___117_1501 = e in
         {
           solver = (uu___117_1501.solver);
           range = r;
           curmodule = (uu___117_1501.curmodule);
           gamma = (uu___117_1501.gamma);
           gamma_cache = (uu___117_1501.gamma_cache);
           modules = (uu___117_1501.modules);
           expected_typ = (uu___117_1501.expected_typ);
           sigtab = (uu___117_1501.sigtab);
           is_pattern = (uu___117_1501.is_pattern);
           instantiate_imp = (uu___117_1501.instantiate_imp);
           effects = (uu___117_1501.effects);
           generalize = (uu___117_1501.generalize);
           letrecs = (uu___117_1501.letrecs);
           top_level = (uu___117_1501.top_level);
           check_uvars = (uu___117_1501.check_uvars);
           use_eq = (uu___117_1501.use_eq);
           is_iface = (uu___117_1501.is_iface);
           admit = (uu___117_1501.admit);
           lax = (uu___117_1501.lax);
           lax_universes = (uu___117_1501.lax_universes);
           type_of = (uu___117_1501.type_of);
           universe_of = (uu___117_1501.universe_of);
           use_bv_sorts = (uu___117_1501.use_bv_sorts);
           qname_and_index = (uu___117_1501.qname_and_index);
           proof_ns = (uu___117_1501.proof_ns);
           synth = (uu___117_1501.synth);
           is_native_tactic = (uu___117_1501.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___118_1518 = env in
      {
        solver = (uu___118_1518.solver);
        range = (uu___118_1518.range);
        curmodule = lid;
        gamma = (uu___118_1518.gamma);
        gamma_cache = (uu___118_1518.gamma_cache);
        modules = (uu___118_1518.modules);
        expected_typ = (uu___118_1518.expected_typ);
        sigtab = (uu___118_1518.sigtab);
        is_pattern = (uu___118_1518.is_pattern);
        instantiate_imp = (uu___118_1518.instantiate_imp);
        effects = (uu___118_1518.effects);
        generalize = (uu___118_1518.generalize);
        letrecs = (uu___118_1518.letrecs);
        top_level = (uu___118_1518.top_level);
        check_uvars = (uu___118_1518.check_uvars);
        use_eq = (uu___118_1518.use_eq);
        is_iface = (uu___118_1518.is_iface);
        admit = (uu___118_1518.admit);
        lax = (uu___118_1518.lax);
        lax_universes = (uu___118_1518.lax_universes);
        type_of = (uu___118_1518.type_of);
        universe_of = (uu___118_1518.universe_of);
        use_bv_sorts = (uu___118_1518.use_bv_sorts);
        qname_and_index = (uu___118_1518.qname_and_index);
        proof_ns = (uu___118_1518.proof_ns);
        synth = (uu___118_1518.synth);
        is_native_tactic = (uu___118_1518.is_native_tactic)
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
    let uu____1540 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1540
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1543  ->
    let uu____1544 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1544
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1566) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1582 = FStar_Syntax_Subst.subst vs t in (us, uu____1582)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___102_1587  ->
    match uu___102_1587 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1601  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1611 = inst_tscheme t in
      match uu____1611 with
      | (us,t1) ->
          let uu____1618 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1618)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1630  ->
          match uu____1630 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1644 =
                         let uu____1645 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1648 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1651 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1652 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1645 uu____1648 uu____1651 uu____1652 in
                       failwith uu____1644)
                    else ();
                    (let uu____1654 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1654))
               | uu____1658 ->
                   let uu____1659 =
                     let uu____1660 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1660 in
                   failwith uu____1659)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1664 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1668 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1672 -> false
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
             | ([],uu____1698) -> Maybe
             | (uu____1702,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1714 -> No in
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
          let uu____1774 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1774 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___103_1795  ->
                   match uu___103_1795 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1818 =
                           let uu____1828 =
                             let uu____1836 = inst_tscheme t in
                             FStar_Util.Inl uu____1836 in
                           (uu____1828, (FStar_Ident.range_of_lid l)) in
                         Some uu____1818
                       else None
                   | Binding_sig
                       (uu____1870,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1872);
                                     FStar_Syntax_Syntax.sigrng = uu____1873;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1874;
                                     FStar_Syntax_Syntax.sigmeta = uu____1875;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1884 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1884
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1911 ->
                             Some t
                         | uu____1915 -> cache t in
                       let uu____1916 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1916 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1956 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1956 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____2000 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2042 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____2042
         then
           let uu____2053 = find_in_sigtab env lid in
           match uu____2053 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2119) ->
          add_sigelts env ses
      | uu____2124 ->
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
            | uu____2133 -> ()))
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
        (fun uu___104_2151  ->
           match uu___104_2151 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2164 -> None)
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
          ((uu____2185,lb::[]),uu____2187,uu____2188) ->
          let uu____2197 =
            let uu____2202 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2208 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2202, uu____2208) in
          Some uu____2197
      | FStar_Syntax_Syntax.Sig_let ((uu____2215,lbs),uu____2217,uu____2218)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2238 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2245 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2245
                   then
                     let uu____2251 =
                       let uu____2256 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2262 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2256, uu____2262) in
                     Some uu____2251
                   else None)
      | uu____2274 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2293 =
          let uu____2298 =
            let uu____2301 =
              let uu____2302 =
                let uu____2305 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2305 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2302) in
            inst_tscheme uu____2301 in
          (uu____2298, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2293
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2319,uu____2320) ->
        let uu____2323 =
          let uu____2328 =
            let uu____2331 =
              let uu____2332 =
                let uu____2335 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2335 in
              (us, uu____2332) in
            inst_tscheme uu____2331 in
          (uu____2328, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2323
    | uu____2346 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2381 =
        match uu____2381 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2431,uvs,t,uu____2434,uu____2435,uu____2436);
                    FStar_Syntax_Syntax.sigrng = uu____2437;
                    FStar_Syntax_Syntax.sigquals = uu____2438;
                    FStar_Syntax_Syntax.sigmeta = uu____2439;_},None
                  )
                 ->
                 let uu____2449 =
                   let uu____2454 = inst_tscheme (uvs, t) in
                   (uu____2454, rng) in
                 Some uu____2449
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2466;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2468;_},None
                  )
                 ->
                 let uu____2476 =
                   let uu____2477 = in_cur_mod env l in uu____2477 = Yes in
                 if uu____2476
                 then
                   let uu____2483 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2483
                    then
                      let uu____2490 =
                        let uu____2495 = inst_tscheme (uvs, t) in
                        (uu____2495, rng) in
                      Some uu____2490
                    else None)
                 else
                   (let uu____2510 =
                      let uu____2515 = inst_tscheme (uvs, t) in
                      (uu____2515, rng) in
                    Some uu____2510)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2528,uu____2529);
                    FStar_Syntax_Syntax.sigrng = uu____2530;
                    FStar_Syntax_Syntax.sigquals = uu____2531;
                    FStar_Syntax_Syntax.sigmeta = uu____2532;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2551 =
                        let uu____2556 = inst_tscheme (uvs, k) in
                        (uu____2556, rng) in
                      Some uu____2551
                  | uu____2565 ->
                      let uu____2566 =
                        let uu____2571 =
                          let uu____2574 =
                            let uu____2575 =
                              let uu____2578 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2578 in
                            (uvs, uu____2575) in
                          inst_tscheme uu____2574 in
                        (uu____2571, rng) in
                      Some uu____2566)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2593,uu____2594);
                    FStar_Syntax_Syntax.sigrng = uu____2595;
                    FStar_Syntax_Syntax.sigquals = uu____2596;
                    FStar_Syntax_Syntax.sigmeta = uu____2597;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2617 =
                        let uu____2622 = inst_tscheme_with (uvs, k) us in
                        (uu____2622, rng) in
                      Some uu____2617
                  | uu____2631 ->
                      let uu____2632 =
                        let uu____2637 =
                          let uu____2640 =
                            let uu____2641 =
                              let uu____2644 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2644 in
                            (uvs, uu____2641) in
                          inst_tscheme_with uu____2640 us in
                        (uu____2637, rng) in
                      Some uu____2632)
             | FStar_Util.Inr se ->
                 let uu____2664 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2675;
                        FStar_Syntax_Syntax.sigrng = uu____2676;
                        FStar_Syntax_Syntax.sigquals = uu____2677;
                        FStar_Syntax_Syntax.sigmeta = uu____2678;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2687 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2664
                   (FStar_Util.map_option
                      (fun uu____2710  ->
                         match uu____2710 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2727 =
        let uu____2733 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2733 mapper in
      match uu____2727 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___119_2785 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___119_2785.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___119_2785.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2785.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2806 = lookup_qname env l in
      match uu____2806 with | None  -> false | Some uu____2826 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2854 = try_lookup_bv env bv in
      match uu____2854 with
      | None  ->
          let uu____2862 =
            let uu____2863 =
              let uu____2866 = variable_not_found bv in (uu____2866, bvr) in
            FStar_Errors.Error uu____2863 in
          raise uu____2862
      | Some (t,r) ->
          let uu____2873 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2874 = FStar_Range.set_use_range r bvr in
          (uu____2873, uu____2874)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2886 = try_lookup_lid_aux env l in
      match uu____2886 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2928 =
            let uu____2933 =
              let uu____2936 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2936) in
            (uu____2933, r1) in
          Some uu____2928
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2953 = try_lookup_lid env l in
      match uu____2953 with
      | None  ->
          let uu____2967 =
            let uu____2968 =
              let uu____2971 = name_not_found l in
              (uu____2971, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2968 in
          raise uu____2967
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_2992  ->
              match uu___105_2992 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2994 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____3005 = lookup_qname env lid in
      match uu____3005 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3020,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3023;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3025;_},None
            ),uu____3026)
          ->
          let uu____3050 =
            let uu____3056 =
              let uu____3059 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____3059) in
            (uu____3056, q) in
          Some uu____3050
      | uu____3068 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3090 = lookup_qname env lid in
      match uu____3090 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3103,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3106;
              FStar_Syntax_Syntax.sigquals = uu____3107;
              FStar_Syntax_Syntax.sigmeta = uu____3108;_},None
            ),uu____3109)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3133 ->
          let uu____3144 =
            let uu____3145 =
              let uu____3148 = name_not_found lid in
              (uu____3148, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3145 in
          raise uu____3144
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3159 = lookup_qname env lid in
      match uu____3159 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3172,uvs,t,uu____3175,uu____3176,uu____3177);
              FStar_Syntax_Syntax.sigrng = uu____3178;
              FStar_Syntax_Syntax.sigquals = uu____3179;
              FStar_Syntax_Syntax.sigmeta = uu____3180;_},None
            ),uu____3181)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3207 ->
          let uu____3218 =
            let uu____3219 =
              let uu____3222 = name_not_found lid in
              (uu____3222, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3219 in
          raise uu____3218
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3234 = lookup_qname env lid in
      match uu____3234 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3248,uu____3249,uu____3250,uu____3251,uu____3252,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3254;
              FStar_Syntax_Syntax.sigquals = uu____3255;
              FStar_Syntax_Syntax.sigmeta = uu____3256;_},uu____3257),uu____3258)
          -> (true, dcs)
      | uu____3288 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3306 = lookup_qname env lid in
      match uu____3306 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3317,uu____3318,uu____3319,l,uu____3321,uu____3322);
              FStar_Syntax_Syntax.sigrng = uu____3323;
              FStar_Syntax_Syntax.sigquals = uu____3324;
              FStar_Syntax_Syntax.sigmeta = uu____3325;_},uu____3326),uu____3327)
          -> l
      | uu____3354 ->
          let uu____3365 =
            let uu____3366 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3366 in
          failwith uu____3365
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
        let uu____3390 = lookup_qname env lid in
        match uu____3390 with
        | Some (FStar_Util.Inr (se,None ),uu____3405) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3431,lbs),uu____3433,uu____3434) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3451 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3451
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3472 -> None)
        | uu____3475 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3496 = lookup_qname env ftv in
      match uu____3496 with
      | Some (FStar_Util.Inr (se,None ),uu____3509) ->
          let uu____3532 = effect_signature se in
          (match uu____3532 with
           | None  -> None
           | Some ((uu____3543,t),r) ->
               let uu____3552 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3552)
      | uu____3553 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3570 = try_lookup_effect_lid env ftv in
      match uu____3570 with
      | None  ->
          let uu____3572 =
            let uu____3573 =
              let uu____3576 = name_not_found ftv in
              (uu____3576, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3573 in
          raise uu____3572
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
        let uu____3590 = lookup_qname env lid0 in
        match uu____3590 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3608);
                FStar_Syntax_Syntax.sigrng = uu____3609;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3611;_},None
              ),uu____3612)
            ->
            let lid1 =
              let uu____3639 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3639 in
            let uu____3640 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_3642  ->
                      match uu___106_3642 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3643 -> false)) in
            if uu____3640
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3656 =
                      let uu____3657 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3658 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3657 uu____3658 in
                    failwith uu____3656) in
               match (binders, univs1) with
               | ([],uu____3664) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3673,uu____3674::uu____3675::uu____3676) ->
                   let uu____3679 =
                     let uu____3680 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3681 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3680 uu____3681 in
                   failwith uu____3679
               | uu____3687 ->
                   let uu____3690 =
                     let uu____3693 =
                       let uu____3694 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3694) in
                     inst_tscheme_with uu____3693 insts in
                   (match uu____3690 with
                    | (uu____3702,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3705 =
                          let uu____3706 = FStar_Syntax_Subst.compress t1 in
                          uu____3706.FStar_Syntax_Syntax.n in
                        (match uu____3705 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3736 -> failwith "Impossible")))
        | uu____3740 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3766 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3766 with
        | None  -> None
        | Some (uu____3773,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3778 = find1 l2 in
            (match uu____3778 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3783 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3783 with
        | Some l1 -> l1
        | None  ->
            let uu____3786 = find1 l in
            (match uu____3786 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3798 = lookup_qname env l1 in
      match uu____3798 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3810;
              FStar_Syntax_Syntax.sigrng = uu____3811;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3813;_},uu____3814),uu____3815)
          -> q
      | uu____3840 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3863 =
          let uu____3864 =
            let uu____3865 = FStar_Util.string_of_int i in
            let uu____3866 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3865 uu____3866 in
          failwith uu____3864 in
        let uu____3867 = lookup_datacon env lid in
        match uu____3867 with
        | (uu____3870,t) ->
            let uu____3872 =
              let uu____3873 = FStar_Syntax_Subst.compress t in
              uu____3873.FStar_Syntax_Syntax.n in
            (match uu____3872 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3877) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3898 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3898 FStar_Pervasives.fst)
             | uu____3903 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3910 = lookup_qname env l in
      match uu____3910 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3921,uu____3922,uu____3923);
              FStar_Syntax_Syntax.sigrng = uu____3924;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3926;_},uu____3927),uu____3928)
          ->
          FStar_Util.for_some
            (fun uu___107_3953  ->
               match uu___107_3953 with
               | FStar_Syntax_Syntax.Projector uu____3954 -> true
               | uu____3957 -> false) quals
      | uu____3958 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3975 = lookup_qname env lid in
      match uu____3975 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3986,uu____3987,uu____3988,uu____3989,uu____3990,uu____3991);
              FStar_Syntax_Syntax.sigrng = uu____3992;
              FStar_Syntax_Syntax.sigquals = uu____3993;
              FStar_Syntax_Syntax.sigmeta = uu____3994;_},uu____3995),uu____3996)
          -> true
      | uu____4023 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4040 = lookup_qname env lid in
      match uu____4040 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4051,uu____4052,uu____4053,uu____4054,uu____4055,uu____4056);
              FStar_Syntax_Syntax.sigrng = uu____4057;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4059;_},uu____4060),uu____4061)
          ->
          FStar_Util.for_some
            (fun uu___108_4090  ->
               match uu___108_4090 with
               | FStar_Syntax_Syntax.RecordType uu____4091 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4096 -> true
               | uu____4101 -> false) quals
      | uu____4102 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4119 = lookup_qname env lid in
      match uu____4119 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4130,uu____4131,uu____4132);
              FStar_Syntax_Syntax.sigrng = uu____4133;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4135;_},uu____4136),uu____4137)
          ->
          FStar_Util.for_some
            (fun uu___109_4166  ->
               match uu___109_4166 with
               | FStar_Syntax_Syntax.Action uu____4167 -> true
               | uu____4168 -> false) quals
      | uu____4169 -> false
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
      let uu____4188 =
        let uu____4189 = FStar_Syntax_Util.un_uinst head1 in
        uu____4189.FStar_Syntax_Syntax.n in
      match uu____4188 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4193 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4231 -> Some false
        | FStar_Util.Inr (se,uu____4240) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4249 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4253 -> Some true
             | uu____4262 -> Some false) in
      let uu____4263 =
        let uu____4265 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4265 mapper in
      match uu____4263 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4292 = lookup_qname env lid in
      match uu____4292 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4303,uu____4304,tps,uu____4306,uu____4307,uu____4308);
              FStar_Syntax_Syntax.sigrng = uu____4309;
              FStar_Syntax_Syntax.sigquals = uu____4310;
              FStar_Syntax_Syntax.sigmeta = uu____4311;_},uu____4312),uu____4313)
          -> FStar_List.length tps
      | uu____4345 ->
          let uu____4356 =
            let uu____4357 =
              let uu____4360 = name_not_found lid in
              (uu____4360, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4357 in
          raise uu____4356
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
           (fun uu____4382  ->
              match uu____4382 with
              | (d,uu____4387) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4396 = effect_decl_opt env l in
      match uu____4396 with
      | None  ->
          let uu____4404 =
            let uu____4405 =
              let uu____4408 = name_not_found l in
              (uu____4408, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4405 in
          raise uu____4404
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
            (let uu____4451 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4475  ->
                       match uu____4475 with
                       | (m1,m2,uu____4483,uu____4484,uu____4485) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4451 with
             | None  ->
                 let uu____4494 =
                   let uu____4495 =
                     let uu____4498 =
                       let uu____4499 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4500 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4499
                         uu____4500 in
                     (uu____4498, (env.range)) in
                   FStar_Errors.Error uu____4495 in
                 raise uu____4494
             | Some (uu____4504,uu____4505,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4552 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4564  ->
            match uu____4564 with
            | (d,uu____4568) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4552 with
  | None  ->
      let uu____4575 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4575
  | Some (md,_q) ->
      let uu____4584 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4584 with
       | (uu____4591,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4599)::(wp,uu____4601)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4623 -> failwith "Impossible"))
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
                 let uu____4659 = get_range env in
                 let uu____4660 =
                   let uu____4663 =
                     let uu____4664 =
                       let uu____4674 =
                         let uu____4676 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4676] in
                       (null_wp, uu____4674) in
                     FStar_Syntax_Syntax.Tm_app uu____4664 in
                   FStar_Syntax_Syntax.mk uu____4663 in
                 uu____4660 None uu____4659 in
               let uu____4686 =
                 let uu____4687 =
                   let uu____4693 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4693] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4687;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4686)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___120_4702 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___120_4702.order);
              joins = (uu___120_4702.joins)
            } in
          let uu___121_4707 = env in
          {
            solver = (uu___121_4707.solver);
            range = (uu___121_4707.range);
            curmodule = (uu___121_4707.curmodule);
            gamma = (uu___121_4707.gamma);
            gamma_cache = (uu___121_4707.gamma_cache);
            modules = (uu___121_4707.modules);
            expected_typ = (uu___121_4707.expected_typ);
            sigtab = (uu___121_4707.sigtab);
            is_pattern = (uu___121_4707.is_pattern);
            instantiate_imp = (uu___121_4707.instantiate_imp);
            effects;
            generalize = (uu___121_4707.generalize);
            letrecs = (uu___121_4707.letrecs);
            top_level = (uu___121_4707.top_level);
            check_uvars = (uu___121_4707.check_uvars);
            use_eq = (uu___121_4707.use_eq);
            is_iface = (uu___121_4707.is_iface);
            admit = (uu___121_4707.admit);
            lax = (uu___121_4707.lax);
            lax_universes = (uu___121_4707.lax_universes);
            type_of = (uu___121_4707.type_of);
            universe_of = (uu___121_4707.universe_of);
            use_bv_sorts = (uu___121_4707.use_bv_sorts);
            qname_and_index = (uu___121_4707.qname_and_index);
            proof_ns = (uu___121_4707.proof_ns);
            synth = (uu___121_4707.synth);
            is_native_tactic = (uu___121_4707.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4724 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4724 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4803 = (e1.mlift).mlift_wp t wp in
                              let uu____4804 = l1 t wp e in
                              l2 t uu____4803 uu____4804))
                | uu____4805 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4840 = inst_tscheme lift_t in
            match uu____4840 with
            | (uu____4845,lift_t1) ->
                let uu____4847 =
                  let uu____4850 =
                    let uu____4851 =
                      let uu____4861 =
                        let uu____4863 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4864 =
                          let uu____4866 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4866] in
                        uu____4863 :: uu____4864 in
                      (lift_t1, uu____4861) in
                    FStar_Syntax_Syntax.Tm_app uu____4851 in
                  FStar_Syntax_Syntax.mk uu____4850 in
                uu____4847 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4911 = inst_tscheme lift_t in
            match uu____4911 with
            | (uu____4916,lift_t1) ->
                let uu____4918 =
                  let uu____4921 =
                    let uu____4922 =
                      let uu____4932 =
                        let uu____4934 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4935 =
                          let uu____4937 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4938 =
                            let uu____4940 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4940] in
                          uu____4937 :: uu____4938 in
                        uu____4934 :: uu____4935 in
                      (lift_t1, uu____4932) in
                    FStar_Syntax_Syntax.Tm_app uu____4922 in
                  FStar_Syntax_Syntax.mk uu____4921 in
                uu____4918 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4981 =
                let uu____4982 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4982
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4981 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4986 =
              let uu____4987 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4987 in
            let uu____4988 =
              let uu____4989 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____5004 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____5004) in
              FStar_Util.dflt "none" uu____4989 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4986
              uu____4988 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____5017  ->
                    match uu____5017 with
                    | (e,uu____5022) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____5035 =
            match uu____5035 with
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
              let uu____5060 =
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
                                    (let uu____5072 =
                                       let uu____5077 =
                                         find_edge order1 (i, k) in
                                       let uu____5079 =
                                         find_edge order1 (k, j) in
                                       (uu____5077, uu____5079) in
                                     match uu____5072 with
                                     | (Some e1,Some e2) ->
                                         let uu____5088 = compose_edges e1 e2 in
                                         [uu____5088]
                                     | uu____5089 -> []))))) in
              FStar_List.append order1 uu____5060 in
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
                   let uu____5104 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5105 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5105
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5104
                   then
                     let uu____5108 =
                       let uu____5109 =
                         let uu____5112 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5113 = get_range env in
                         (uu____5112, uu____5113) in
                       FStar_Errors.Error uu____5109 in
                     raise uu____5108
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
                                            let uu____5176 =
                                              let uu____5181 =
                                                find_edge order2 (i, k) in
                                              let uu____5183 =
                                                find_edge order2 (j, k) in
                                              (uu____5181, uu____5183) in
                                            match uu____5176 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5206,uu____5207)
                                                     ->
                                                     let uu____5211 =
                                                       let uu____5214 =
                                                         let uu____5215 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5215 in
                                                       let uu____5217 =
                                                         let uu____5218 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5218 in
                                                       (uu____5214,
                                                         uu____5217) in
                                                     (match uu____5211 with
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
                                            | uu____5237 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___122_5276 = env.effects in
              { decls = (uu___122_5276.decls); order = order2; joins } in
            let uu___123_5277 = env in
            {
              solver = (uu___123_5277.solver);
              range = (uu___123_5277.range);
              curmodule = (uu___123_5277.curmodule);
              gamma = (uu___123_5277.gamma);
              gamma_cache = (uu___123_5277.gamma_cache);
              modules = (uu___123_5277.modules);
              expected_typ = (uu___123_5277.expected_typ);
              sigtab = (uu___123_5277.sigtab);
              is_pattern = (uu___123_5277.is_pattern);
              instantiate_imp = (uu___123_5277.instantiate_imp);
              effects;
              generalize = (uu___123_5277.generalize);
              letrecs = (uu___123_5277.letrecs);
              top_level = (uu___123_5277.top_level);
              check_uvars = (uu___123_5277.check_uvars);
              use_eq = (uu___123_5277.use_eq);
              is_iface = (uu___123_5277.is_iface);
              admit = (uu___123_5277.admit);
              lax = (uu___123_5277.lax);
              lax_universes = (uu___123_5277.lax_universes);
              type_of = (uu___123_5277.type_of);
              universe_of = (uu___123_5277.universe_of);
              use_bv_sorts = (uu___123_5277.use_bv_sorts);
              qname_and_index = (uu___123_5277.qname_and_index);
              proof_ns = (uu___123_5277.proof_ns);
              synth = (uu___123_5277.synth);
              is_native_tactic = (uu___123_5277.is_native_tactic)
            }))
      | uu____5278 -> env
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
        | uu____5300 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5308 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5308 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5318 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5318 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5335 =
                     let uu____5336 =
                       let uu____5339 =
                         let uu____5340 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5346 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5354 =
                           let uu____5355 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5355 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5340 uu____5346 uu____5354 in
                       (uu____5339, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5336 in
                   raise uu____5335)
                else ();
                (let inst1 =
                   let uu____5359 =
                     let uu____5365 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5365 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5372  ->
                        fun uu____5373  ->
                          match (uu____5372, uu____5373) with
                          | ((x,uu____5387),(t,uu____5389)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5359 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5404 =
                     let uu___124_5405 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___124_5405.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___124_5405.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___124_5405.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___124_5405.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5404
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5435 =
    let uu____5440 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5440 in
  match uu____5435 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5456 =
        only_reifiable &&
          (let uu____5457 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5457) in
      if uu____5456
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5470 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5472 =
               let uu____5481 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5481) in
             (match uu____5472 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5515 =
                    let uu____5518 = get_range env in
                    let uu____5519 =
                      let uu____5522 =
                        let uu____5523 =
                          let uu____5533 =
                            let uu____5535 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5535; wp] in
                          (repr, uu____5533) in
                        FStar_Syntax_Syntax.Tm_app uu____5523 in
                      FStar_Syntax_Syntax.mk uu____5522 in
                    uu____5519 None uu____5518 in
                  Some uu____5515))
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
          let uu____5579 =
            let uu____5580 =
              let uu____5583 =
                let uu____5584 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5584 in
              let uu____5585 = get_range env in (uu____5583, uu____5585) in
            FStar_Errors.Error uu____5580 in
          raise uu____5579 in
        let uu____5586 = effect_repr_aux true env c u_c in
        match uu____5586 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable: env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5618 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5625 =
        let uu____5626 = FStar_Syntax_Subst.compress t in
        uu____5626.FStar_Syntax_Syntax.n in
      match uu____5625 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5629,c) ->
          is_reifiable_comp env c
      | uu____5641 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5659)::uu____5660 -> x :: rest
        | (Binding_sig_inst uu____5665)::uu____5666 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5675 = push1 x rest1 in local :: uu____5675 in
      let uu___125_5677 = env in
      let uu____5678 = push1 s env.gamma in
      {
        solver = (uu___125_5677.solver);
        range = (uu___125_5677.range);
        curmodule = (uu___125_5677.curmodule);
        gamma = uu____5678;
        gamma_cache = (uu___125_5677.gamma_cache);
        modules = (uu___125_5677.modules);
        expected_typ = (uu___125_5677.expected_typ);
        sigtab = (uu___125_5677.sigtab);
        is_pattern = (uu___125_5677.is_pattern);
        instantiate_imp = (uu___125_5677.instantiate_imp);
        effects = (uu___125_5677.effects);
        generalize = (uu___125_5677.generalize);
        letrecs = (uu___125_5677.letrecs);
        top_level = (uu___125_5677.top_level);
        check_uvars = (uu___125_5677.check_uvars);
        use_eq = (uu___125_5677.use_eq);
        is_iface = (uu___125_5677.is_iface);
        admit = (uu___125_5677.admit);
        lax = (uu___125_5677.lax);
        lax_universes = (uu___125_5677.lax_universes);
        type_of = (uu___125_5677.type_of);
        universe_of = (uu___125_5677.universe_of);
        use_bv_sorts = (uu___125_5677.use_bv_sorts);
        qname_and_index = (uu___125_5677.qname_and_index);
        proof_ns = (uu___125_5677.proof_ns);
        synth = (uu___125_5677.synth);
        is_native_tactic = (uu___125_5677.is_native_tactic)
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
      let uu___126_5705 = env in
      {
        solver = (uu___126_5705.solver);
        range = (uu___126_5705.range);
        curmodule = (uu___126_5705.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___126_5705.gamma_cache);
        modules = (uu___126_5705.modules);
        expected_typ = (uu___126_5705.expected_typ);
        sigtab = (uu___126_5705.sigtab);
        is_pattern = (uu___126_5705.is_pattern);
        instantiate_imp = (uu___126_5705.instantiate_imp);
        effects = (uu___126_5705.effects);
        generalize = (uu___126_5705.generalize);
        letrecs = (uu___126_5705.letrecs);
        top_level = (uu___126_5705.top_level);
        check_uvars = (uu___126_5705.check_uvars);
        use_eq = (uu___126_5705.use_eq);
        is_iface = (uu___126_5705.is_iface);
        admit = (uu___126_5705.admit);
        lax = (uu___126_5705.lax);
        lax_universes = (uu___126_5705.lax_universes);
        type_of = (uu___126_5705.type_of);
        universe_of = (uu___126_5705.universe_of);
        use_bv_sorts = (uu___126_5705.use_bv_sorts);
        qname_and_index = (uu___126_5705.qname_and_index);
        proof_ns = (uu___126_5705.proof_ns);
        synth = (uu___126_5705.synth);
        is_native_tactic = (uu___126_5705.is_native_tactic)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___127_5726 = env in
             {
               solver = (uu___127_5726.solver);
               range = (uu___127_5726.range);
               curmodule = (uu___127_5726.curmodule);
               gamma = rest;
               gamma_cache = (uu___127_5726.gamma_cache);
               modules = (uu___127_5726.modules);
               expected_typ = (uu___127_5726.expected_typ);
               sigtab = (uu___127_5726.sigtab);
               is_pattern = (uu___127_5726.is_pattern);
               instantiate_imp = (uu___127_5726.instantiate_imp);
               effects = (uu___127_5726.effects);
               generalize = (uu___127_5726.generalize);
               letrecs = (uu___127_5726.letrecs);
               top_level = (uu___127_5726.top_level);
               check_uvars = (uu___127_5726.check_uvars);
               use_eq = (uu___127_5726.use_eq);
               is_iface = (uu___127_5726.is_iface);
               admit = (uu___127_5726.admit);
               lax = (uu___127_5726.lax);
               lax_universes = (uu___127_5726.lax_universes);
               type_of = (uu___127_5726.type_of);
               universe_of = (uu___127_5726.universe_of);
               use_bv_sorts = (uu___127_5726.use_bv_sorts);
               qname_and_index = (uu___127_5726.qname_and_index);
               proof_ns = (uu___127_5726.proof_ns);
               synth = (uu___127_5726.synth);
               is_native_tactic = (uu___127_5726.is_native_tactic)
             }))
    | uu____5727 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5740  ->
             match uu____5740 with | (x,uu____5744) -> push_bv env1 x) env bs
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
            let uu___128_5764 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_5764.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_5764.FStar_Syntax_Syntax.index);
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
      (let uu___129_5794 = env in
       {
         solver = (uu___129_5794.solver);
         range = (uu___129_5794.range);
         curmodule = (uu___129_5794.curmodule);
         gamma = [];
         gamma_cache = (uu___129_5794.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___129_5794.sigtab);
         is_pattern = (uu___129_5794.is_pattern);
         instantiate_imp = (uu___129_5794.instantiate_imp);
         effects = (uu___129_5794.effects);
         generalize = (uu___129_5794.generalize);
         letrecs = (uu___129_5794.letrecs);
         top_level = (uu___129_5794.top_level);
         check_uvars = (uu___129_5794.check_uvars);
         use_eq = (uu___129_5794.use_eq);
         is_iface = (uu___129_5794.is_iface);
         admit = (uu___129_5794.admit);
         lax = (uu___129_5794.lax);
         lax_universes = (uu___129_5794.lax_universes);
         type_of = (uu___129_5794.type_of);
         universe_of = (uu___129_5794.universe_of);
         use_bv_sorts = (uu___129_5794.use_bv_sorts);
         qname_and_index = (uu___129_5794.qname_and_index);
         proof_ns = (uu___129_5794.proof_ns);
         synth = (uu___129_5794.synth);
         is_native_tactic = (uu___129_5794.is_native_tactic)
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
        let uu____5818 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5818 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5834 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5834)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___130_5844 = env in
      {
        solver = (uu___130_5844.solver);
        range = (uu___130_5844.range);
        curmodule = (uu___130_5844.curmodule);
        gamma = (uu___130_5844.gamma);
        gamma_cache = (uu___130_5844.gamma_cache);
        modules = (uu___130_5844.modules);
        expected_typ = (Some t);
        sigtab = (uu___130_5844.sigtab);
        is_pattern = (uu___130_5844.is_pattern);
        instantiate_imp = (uu___130_5844.instantiate_imp);
        effects = (uu___130_5844.effects);
        generalize = (uu___130_5844.generalize);
        letrecs = (uu___130_5844.letrecs);
        top_level = (uu___130_5844.top_level);
        check_uvars = (uu___130_5844.check_uvars);
        use_eq = false;
        is_iface = (uu___130_5844.is_iface);
        admit = (uu___130_5844.admit);
        lax = (uu___130_5844.lax);
        lax_universes = (uu___130_5844.lax_universes);
        type_of = (uu___130_5844.type_of);
        universe_of = (uu___130_5844.universe_of);
        use_bv_sorts = (uu___130_5844.use_bv_sorts);
        qname_and_index = (uu___130_5844.qname_and_index);
        proof_ns = (uu___130_5844.proof_ns);
        synth = (uu___130_5844.synth);
        is_native_tactic = (uu___130_5844.is_native_tactic)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5860 = expected_typ env_ in
    ((let uu___131_5863 = env_ in
      {
        solver = (uu___131_5863.solver);
        range = (uu___131_5863.range);
        curmodule = (uu___131_5863.curmodule);
        gamma = (uu___131_5863.gamma);
        gamma_cache = (uu___131_5863.gamma_cache);
        modules = (uu___131_5863.modules);
        expected_typ = None;
        sigtab = (uu___131_5863.sigtab);
        is_pattern = (uu___131_5863.is_pattern);
        instantiate_imp = (uu___131_5863.instantiate_imp);
        effects = (uu___131_5863.effects);
        generalize = (uu___131_5863.generalize);
        letrecs = (uu___131_5863.letrecs);
        top_level = (uu___131_5863.top_level);
        check_uvars = (uu___131_5863.check_uvars);
        use_eq = false;
        is_iface = (uu___131_5863.is_iface);
        admit = (uu___131_5863.admit);
        lax = (uu___131_5863.lax);
        lax_universes = (uu___131_5863.lax_universes);
        type_of = (uu___131_5863.type_of);
        universe_of = (uu___131_5863.universe_of);
        use_bv_sorts = (uu___131_5863.use_bv_sorts);
        qname_and_index = (uu___131_5863.qname_and_index);
        proof_ns = (uu___131_5863.proof_ns);
        synth = (uu___131_5863.synth);
        is_native_tactic = (uu___131_5863.is_native_tactic)
      }), uu____5860)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5874 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___110_5878  ->
                    match uu___110_5878 with
                    | Binding_sig (uu____5880,se) -> [se]
                    | uu____5884 -> [])) in
          FStar_All.pipe_right uu____5874 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___132_5889 = env in
       {
         solver = (uu___132_5889.solver);
         range = (uu___132_5889.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___132_5889.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___132_5889.expected_typ);
         sigtab = (uu___132_5889.sigtab);
         is_pattern = (uu___132_5889.is_pattern);
         instantiate_imp = (uu___132_5889.instantiate_imp);
         effects = (uu___132_5889.effects);
         generalize = (uu___132_5889.generalize);
         letrecs = (uu___132_5889.letrecs);
         top_level = (uu___132_5889.top_level);
         check_uvars = (uu___132_5889.check_uvars);
         use_eq = (uu___132_5889.use_eq);
         is_iface = (uu___132_5889.is_iface);
         admit = (uu___132_5889.admit);
         lax = (uu___132_5889.lax);
         lax_universes = (uu___132_5889.lax_universes);
         type_of = (uu___132_5889.type_of);
         universe_of = (uu___132_5889.universe_of);
         use_bv_sorts = (uu___132_5889.use_bv_sorts);
         qname_and_index = (uu___132_5889.qname_and_index);
         proof_ns = (uu___132_5889.proof_ns);
         synth = (uu___132_5889.synth);
         is_native_tactic = (uu___132_5889.is_native_tactic)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5939)::tl1 -> aux out tl1
      | (Binding_lid (uu____5942,(uu____5943,t)))::tl1 ->
          let uu____5952 =
            let uu____5956 = FStar_Syntax_Free.uvars t in ext out uu____5956 in
          aux uu____5952 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5960;
            FStar_Syntax_Syntax.index = uu____5961;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5967 =
            let uu____5971 = FStar_Syntax_Free.uvars t in ext out uu____5971 in
          aux uu____5967 tl1
      | (Binding_sig uu____5975)::uu____5976 -> out
      | (Binding_sig_inst uu____5981)::uu____5982 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6019)::tl1 -> aux out tl1
      | (Binding_univ uu____6026)::tl1 -> aux out tl1
      | (Binding_lid (uu____6029,(uu____6030,t)))::tl1 ->
          let uu____6039 =
            let uu____6041 = FStar_Syntax_Free.univs t in ext out uu____6041 in
          aux uu____6039 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6043;
            FStar_Syntax_Syntax.index = uu____6044;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6050 =
            let uu____6052 = FStar_Syntax_Free.univs t in ext out uu____6052 in
          aux uu____6050 tl1
      | (Binding_sig uu____6054)::uu____6055 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6092)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6102 = FStar_Util.set_add uname out in aux uu____6102 tl1
      | (Binding_lid (uu____6104,(uu____6105,t)))::tl1 ->
          let uu____6114 =
            let uu____6116 = FStar_Syntax_Free.univnames t in
            ext out uu____6116 in
          aux uu____6114 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6118;
            FStar_Syntax_Syntax.index = uu____6119;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6125 =
            let uu____6127 = FStar_Syntax_Free.univnames t in
            ext out uu____6127 in
          aux uu____6125 tl1
      | (Binding_sig uu____6129)::uu____6130 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_6146  ->
            match uu___111_6146 with
            | Binding_var x -> [x]
            | Binding_lid uu____6149 -> []
            | Binding_sig uu____6152 -> []
            | Binding_univ uu____6156 -> []
            | Binding_sig_inst uu____6157 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6167 =
      let uu____6169 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6169
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6167 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6185 =
      let uu____6186 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___112_6190  ->
                match uu___112_6190 with
                | Binding_var x ->
                    let uu____6192 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6192
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6195) ->
                    let uu____6196 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6196
                | Binding_sig (ls,uu____6198) ->
                    let uu____6201 =
                      let uu____6202 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6202
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6201
                | Binding_sig_inst (ls,uu____6208,uu____6209) ->
                    let uu____6212 =
                      let uu____6213 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6213
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6212)) in
      FStar_All.pipe_right uu____6186 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6185 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6225 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6225
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6242  ->
                 fun uu____6243  ->
                   match (uu____6242, uu____6243) with
                   | ((b1,uu____6253),(b2,uu____6255)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___113_6298  ->
             match uu___113_6298 with
             | Binding_sig (lids,uu____6302) -> FStar_List.append lids keys
             | uu____6305 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6307  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6332) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6344,uu____6345) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6369 = list_prefix p path1 in
            if uu____6369 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6379 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6379
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___133_6399 = e in
            {
              solver = (uu___133_6399.solver);
              range = (uu___133_6399.range);
              curmodule = (uu___133_6399.curmodule);
              gamma = (uu___133_6399.gamma);
              gamma_cache = (uu___133_6399.gamma_cache);
              modules = (uu___133_6399.modules);
              expected_typ = (uu___133_6399.expected_typ);
              sigtab = (uu___133_6399.sigtab);
              is_pattern = (uu___133_6399.is_pattern);
              instantiate_imp = (uu___133_6399.instantiate_imp);
              effects = (uu___133_6399.effects);
              generalize = (uu___133_6399.generalize);
              letrecs = (uu___133_6399.letrecs);
              top_level = (uu___133_6399.top_level);
              check_uvars = (uu___133_6399.check_uvars);
              use_eq = (uu___133_6399.use_eq);
              is_iface = (uu___133_6399.is_iface);
              admit = (uu___133_6399.admit);
              lax = (uu___133_6399.lax);
              lax_universes = (uu___133_6399.lax_universes);
              type_of = (uu___133_6399.type_of);
              universe_of = (uu___133_6399.universe_of);
              use_bv_sorts = (uu___133_6399.use_bv_sorts);
              qname_and_index = (uu___133_6399.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___133_6399.synth);
              is_native_tactic = (uu___133_6399.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___134_6418 = e in
    {
      solver = (uu___134_6418.solver);
      range = (uu___134_6418.range);
      curmodule = (uu___134_6418.curmodule);
      gamma = (uu___134_6418.gamma);
      gamma_cache = (uu___134_6418.gamma_cache);
      modules = (uu___134_6418.modules);
      expected_typ = (uu___134_6418.expected_typ);
      sigtab = (uu___134_6418.sigtab);
      is_pattern = (uu___134_6418.is_pattern);
      instantiate_imp = (uu___134_6418.instantiate_imp);
      effects = (uu___134_6418.effects);
      generalize = (uu___134_6418.generalize);
      letrecs = (uu___134_6418.letrecs);
      top_level = (uu___134_6418.top_level);
      check_uvars = (uu___134_6418.check_uvars);
      use_eq = (uu___134_6418.use_eq);
      is_iface = (uu___134_6418.is_iface);
      admit = (uu___134_6418.admit);
      lax = (uu___134_6418.lax);
      lax_universes = (uu___134_6418.lax_universes);
      type_of = (uu___134_6418.type_of);
      universe_of = (uu___134_6418.universe_of);
      use_bv_sorts = (uu___134_6418.use_bv_sorts);
      qname_and_index = (uu___134_6418.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___134_6418.synth);
      is_native_tactic = (uu___134_6418.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6427::rest ->
        let uu___135_6430 = e in
        {
          solver = (uu___135_6430.solver);
          range = (uu___135_6430.range);
          curmodule = (uu___135_6430.curmodule);
          gamma = (uu___135_6430.gamma);
          gamma_cache = (uu___135_6430.gamma_cache);
          modules = (uu___135_6430.modules);
          expected_typ = (uu___135_6430.expected_typ);
          sigtab = (uu___135_6430.sigtab);
          is_pattern = (uu___135_6430.is_pattern);
          instantiate_imp = (uu___135_6430.instantiate_imp);
          effects = (uu___135_6430.effects);
          generalize = (uu___135_6430.generalize);
          letrecs = (uu___135_6430.letrecs);
          top_level = (uu___135_6430.top_level);
          check_uvars = (uu___135_6430.check_uvars);
          use_eq = (uu___135_6430.use_eq);
          is_iface = (uu___135_6430.is_iface);
          admit = (uu___135_6430.admit);
          lax = (uu___135_6430.lax);
          lax_universes = (uu___135_6430.lax_universes);
          type_of = (uu___135_6430.type_of);
          universe_of = (uu___135_6430.universe_of);
          use_bv_sorts = (uu___135_6430.use_bv_sorts);
          qname_and_index = (uu___135_6430.qname_and_index);
          proof_ns = rest;
          synth = (uu___135_6430.synth);
          is_native_tactic = (uu___135_6430.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___136_6440 = e in
      {
        solver = (uu___136_6440.solver);
        range = (uu___136_6440.range);
        curmodule = (uu___136_6440.curmodule);
        gamma = (uu___136_6440.gamma);
        gamma_cache = (uu___136_6440.gamma_cache);
        modules = (uu___136_6440.modules);
        expected_typ = (uu___136_6440.expected_typ);
        sigtab = (uu___136_6440.sigtab);
        is_pattern = (uu___136_6440.is_pattern);
        instantiate_imp = (uu___136_6440.instantiate_imp);
        effects = (uu___136_6440.effects);
        generalize = (uu___136_6440.generalize);
        letrecs = (uu___136_6440.letrecs);
        top_level = (uu___136_6440.top_level);
        check_uvars = (uu___136_6440.check_uvars);
        use_eq = (uu___136_6440.use_eq);
        is_iface = (uu___136_6440.is_iface);
        admit = (uu___136_6440.admit);
        lax = (uu___136_6440.lax);
        lax_universes = (uu___136_6440.lax_universes);
        type_of = (uu___136_6440.type_of);
        universe_of = (uu___136_6440.universe_of);
        use_bv_sorts = (uu___136_6440.use_bv_sorts);
        qname_and_index = (uu___136_6440.qname_and_index);
        proof_ns = ns;
        synth = (uu___136_6440.synth);
        is_native_tactic = (uu___136_6440.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6458 =
        FStar_List.map
          (fun fpns  ->
             let uu____6469 =
               let uu____6470 =
                 let uu____6471 =
                   FStar_List.map
                     (fun uu____6476  ->
                        match uu____6476 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6471 in
               Prims.strcat uu____6470 "]" in
             Prims.strcat "[" uu____6469) pns in
      FStar_String.concat ";" uu____6458 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6485  -> ());
    push = (fun uu____6486  -> ());
    pop = (fun uu____6487  -> ());
    mark = (fun uu____6488  -> ());
    reset_mark = (fun uu____6489  -> ());
    commit_mark = (fun uu____6490  -> ());
    encode_modul = (fun uu____6491  -> fun uu____6492  -> ());
    encode_sig = (fun uu____6493  -> fun uu____6494  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6501  -> fun uu____6502  -> fun uu____6503  -> ());
    is_trivial = (fun uu____6507  -> fun uu____6508  -> false);
    finish = (fun uu____6509  -> ());
    refresh = (fun uu____6510  -> ())
  }