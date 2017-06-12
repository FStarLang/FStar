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
      | (NoDelta ,uu____978) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____979,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____980,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____981 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____991 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____999 =
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
          let uu____1038 = new_gamma_cache () in
          let uu____1040 = new_sigtab () in
          let uu____1042 =
            let uu____1043 = FStar_Options.using_facts_from () in
            match uu____1043 with
            | Some ns ->
                let uu____1049 =
                  let uu____1054 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____1054 [([], false)] in
                [uu____1049]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1038;
            modules = [];
            expected_typ = None;
            sigtab = uu____1040;
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
            proof_ns = uu____1042;
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
  fun uu____1135  ->
    let uu____1136 = FStar_ST.read query_indices in
    match uu____1136 with
    | [] -> failwith "Empty query indices!"
    | uu____1150 ->
        let uu____1155 =
          let uu____1160 =
            let uu____1164 = FStar_ST.read query_indices in
            FStar_List.hd uu____1164 in
          let uu____1178 = FStar_ST.read query_indices in uu____1160 ::
            uu____1178 in
        FStar_ST.write query_indices uu____1155
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1200  ->
    let uu____1201 = FStar_ST.read query_indices in
    match uu____1201 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1237  ->
    match uu____1237 with
    | (l,n1) ->
        let uu____1242 = FStar_ST.read query_indices in
        (match uu____1242 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1276 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1286  ->
    let uu____1287 = FStar_ST.read query_indices in FStar_List.hd uu____1287
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1303  ->
    let uu____1304 = FStar_ST.read query_indices in
    match uu____1304 with
    | hd1::uu____1316::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1343 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1357 =
       let uu____1359 = FStar_ST.read stack in env :: uu____1359 in
     FStar_ST.write stack uu____1357);
    (let uu___112_1367 = env in
     let uu____1368 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1370 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1367.solver);
       range = (uu___112_1367.range);
       curmodule = (uu___112_1367.curmodule);
       gamma = (uu___112_1367.gamma);
       gamma_cache = uu____1368;
       modules = (uu___112_1367.modules);
       expected_typ = (uu___112_1367.expected_typ);
       sigtab = uu____1370;
       is_pattern = (uu___112_1367.is_pattern);
       instantiate_imp = (uu___112_1367.instantiate_imp);
       effects = (uu___112_1367.effects);
       generalize = (uu___112_1367.generalize);
       letrecs = (uu___112_1367.letrecs);
       top_level = (uu___112_1367.top_level);
       check_uvars = (uu___112_1367.check_uvars);
       use_eq = (uu___112_1367.use_eq);
       is_iface = (uu___112_1367.is_iface);
       admit = (uu___112_1367.admit);
       lax = (uu___112_1367.lax);
       lax_universes = (uu___112_1367.lax_universes);
       type_of = (uu___112_1367.type_of);
       universe_of = (uu___112_1367.universe_of);
       use_bv_sorts = (uu___112_1367.use_bv_sorts);
       qname_and_index = (uu___112_1367.qname_and_index);
       proof_ns = (uu___112_1367.proof_ns);
       synth = (uu___112_1367.synth)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1374  ->
    let uu____1375 = FStar_ST.read stack in
    match uu____1375 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1387 -> failwith "Impossible: Too many pops"
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
    (let uu____1419 = pop_stack () in ());
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
        let uu____1438 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1450  ->
                  match uu____1450 with
                  | (m,uu____1454) -> FStar_Ident.lid_equals l m)) in
        (match uu____1438 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1459 = env in
               {
                 solver = (uu___113_1459.solver);
                 range = (uu___113_1459.range);
                 curmodule = (uu___113_1459.curmodule);
                 gamma = (uu___113_1459.gamma);
                 gamma_cache = (uu___113_1459.gamma_cache);
                 modules = (uu___113_1459.modules);
                 expected_typ = (uu___113_1459.expected_typ);
                 sigtab = (uu___113_1459.sigtab);
                 is_pattern = (uu___113_1459.is_pattern);
                 instantiate_imp = (uu___113_1459.instantiate_imp);
                 effects = (uu___113_1459.effects);
                 generalize = (uu___113_1459.generalize);
                 letrecs = (uu___113_1459.letrecs);
                 top_level = (uu___113_1459.top_level);
                 check_uvars = (uu___113_1459.check_uvars);
                 use_eq = (uu___113_1459.use_eq);
                 is_iface = (uu___113_1459.is_iface);
                 admit = (uu___113_1459.admit);
                 lax = (uu___113_1459.lax);
                 lax_universes = (uu___113_1459.lax_universes);
                 type_of = (uu___113_1459.type_of);
                 universe_of = (uu___113_1459.universe_of);
                 use_bv_sorts = (uu___113_1459.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_1459.proof_ns);
                 synth = (uu___113_1459.synth)
               }))
         | Some (uu____1462,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1468 = env in
               {
                 solver = (uu___114_1468.solver);
                 range = (uu___114_1468.range);
                 curmodule = (uu___114_1468.curmodule);
                 gamma = (uu___114_1468.gamma);
                 gamma_cache = (uu___114_1468.gamma_cache);
                 modules = (uu___114_1468.modules);
                 expected_typ = (uu___114_1468.expected_typ);
                 sigtab = (uu___114_1468.sigtab);
                 is_pattern = (uu___114_1468.is_pattern);
                 instantiate_imp = (uu___114_1468.instantiate_imp);
                 effects = (uu___114_1468.effects);
                 generalize = (uu___114_1468.generalize);
                 letrecs = (uu___114_1468.letrecs);
                 top_level = (uu___114_1468.top_level);
                 check_uvars = (uu___114_1468.check_uvars);
                 use_eq = (uu___114_1468.use_eq);
                 is_iface = (uu___114_1468.is_iface);
                 admit = (uu___114_1468.admit);
                 lax = (uu___114_1468.lax);
                 lax_universes = (uu___114_1468.lax_universes);
                 type_of = (uu___114_1468.type_of);
                 universe_of = (uu___114_1468.universe_of);
                 use_bv_sorts = (uu___114_1468.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_1468.proof_ns);
                 synth = (uu___114_1468.synth)
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
        (let uu___115_1484 = e in
         {
           solver = (uu___115_1484.solver);
           range = r;
           curmodule = (uu___115_1484.curmodule);
           gamma = (uu___115_1484.gamma);
           gamma_cache = (uu___115_1484.gamma_cache);
           modules = (uu___115_1484.modules);
           expected_typ = (uu___115_1484.expected_typ);
           sigtab = (uu___115_1484.sigtab);
           is_pattern = (uu___115_1484.is_pattern);
           instantiate_imp = (uu___115_1484.instantiate_imp);
           effects = (uu___115_1484.effects);
           generalize = (uu___115_1484.generalize);
           letrecs = (uu___115_1484.letrecs);
           top_level = (uu___115_1484.top_level);
           check_uvars = (uu___115_1484.check_uvars);
           use_eq = (uu___115_1484.use_eq);
           is_iface = (uu___115_1484.is_iface);
           admit = (uu___115_1484.admit);
           lax = (uu___115_1484.lax);
           lax_universes = (uu___115_1484.lax_universes);
           type_of = (uu___115_1484.type_of);
           universe_of = (uu___115_1484.universe_of);
           use_bv_sorts = (uu___115_1484.use_bv_sorts);
           qname_and_index = (uu___115_1484.qname_and_index);
           proof_ns = (uu___115_1484.proof_ns);
           synth = (uu___115_1484.synth)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1501 = env in
      {
        solver = (uu___116_1501.solver);
        range = (uu___116_1501.range);
        curmodule = lid;
        gamma = (uu___116_1501.gamma);
        gamma_cache = (uu___116_1501.gamma_cache);
        modules = (uu___116_1501.modules);
        expected_typ = (uu___116_1501.expected_typ);
        sigtab = (uu___116_1501.sigtab);
        is_pattern = (uu___116_1501.is_pattern);
        instantiate_imp = (uu___116_1501.instantiate_imp);
        effects = (uu___116_1501.effects);
        generalize = (uu___116_1501.generalize);
        letrecs = (uu___116_1501.letrecs);
        top_level = (uu___116_1501.top_level);
        check_uvars = (uu___116_1501.check_uvars);
        use_eq = (uu___116_1501.use_eq);
        is_iface = (uu___116_1501.is_iface);
        admit = (uu___116_1501.admit);
        lax = (uu___116_1501.lax);
        lax_universes = (uu___116_1501.lax_universes);
        type_of = (uu___116_1501.type_of);
        universe_of = (uu___116_1501.universe_of);
        use_bv_sorts = (uu___116_1501.use_bv_sorts);
        qname_and_index = (uu___116_1501.qname_and_index);
        proof_ns = (uu___116_1501.proof_ns);
        synth = (uu___116_1501.synth)
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
    let uu____1523 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1523
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1526  ->
    let uu____1527 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1527
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1549) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1568 = FStar_Syntax_Subst.subst vs t in (us, uu____1568)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1573  ->
    match uu___100_1573 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1587  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1597 = inst_tscheme t in
      match uu____1597 with
      | (us,t1) ->
          let uu____1604 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1604)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1616  ->
          match uu____1616 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1634 =
                         let uu____1635 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1640 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1645 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1646 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1635 uu____1640 uu____1645 uu____1646 in
                       failwith uu____1634)
                    else ();
                    (let uu____1648 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1648))
               | uu____1652 ->
                   let uu____1653 =
                     let uu____1654 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1654 in
                   failwith uu____1653)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1658 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1662 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1666 -> false
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
             | ([],uu____1692) -> Maybe
             | (uu____1696,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1708 -> No in
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
          let uu____1768 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1768 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1789  ->
                   match uu___101_1789 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1812 =
                           let uu____1822 =
                             let uu____1830 = inst_tscheme t in
                             FStar_Util.Inl uu____1830 in
                           (uu____1822, (FStar_Ident.range_of_lid l)) in
                         Some uu____1812
                       else None
                   | Binding_sig
                       (uu____1864,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1866);
                                     FStar_Syntax_Syntax.sigrng = uu____1867;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1868;
                                     FStar_Syntax_Syntax.sigmeta = uu____1869;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1878 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1878
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1905 ->
                             Some t
                         | uu____1909 -> cache t in
                       let uu____1910 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1910 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1950 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1950 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1994 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2036 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____2036
         then
           let uu____2047 = find_in_sigtab env lid in
           match uu____2047 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2113) ->
          add_sigelts env ses
      | uu____2118 ->
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
            | uu____2127 -> ()))
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
        (fun uu___102_2145  ->
           match uu___102_2145 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2158 -> None)
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
          ((uu____2179,lb::[]),uu____2181,uu____2182) ->
          let uu____2191 =
            let uu____2196 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2202 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2196, uu____2202) in
          Some uu____2191
      | FStar_Syntax_Syntax.Sig_let ((uu____2209,lbs),uu____2211,uu____2212)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2232 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2239 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2239
                   then
                     let uu____2245 =
                       let uu____2250 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2256 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2250, uu____2256) in
                     Some uu____2245
                   else None)
      | uu____2268 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2287 =
          let uu____2292 =
            let uu____2295 =
              let uu____2296 =
                let uu____2299 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2299 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2296) in
            inst_tscheme uu____2295 in
          (uu____2292, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2287
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2313,uu____2314) ->
        let uu____2317 =
          let uu____2322 =
            let uu____2325 =
              let uu____2326 =
                let uu____2329 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2329 in
              (us, uu____2326) in
            inst_tscheme uu____2325 in
          (uu____2322, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2317
    | uu____2340 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2375 =
        match uu____2375 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2425,uvs,t,uu____2428,uu____2429,uu____2430);
                    FStar_Syntax_Syntax.sigrng = uu____2431;
                    FStar_Syntax_Syntax.sigquals = uu____2432;
                    FStar_Syntax_Syntax.sigmeta = uu____2433;_},None
                  )
                 ->
                 let uu____2443 =
                   let uu____2448 = inst_tscheme (uvs, t) in
                   (uu____2448, rng) in
                 Some uu____2443
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2460;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2462;_},None
                  )
                 ->
                 let uu____2470 =
                   let uu____2471 = in_cur_mod env l in uu____2471 = Yes in
                 if uu____2470
                 then
                   let uu____2477 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2477
                    then
                      let uu____2484 =
                        let uu____2489 = inst_tscheme (uvs, t) in
                        (uu____2489, rng) in
                      Some uu____2484
                    else None)
                 else
                   (let uu____2504 =
                      let uu____2509 = inst_tscheme (uvs, t) in
                      (uu____2509, rng) in
                    Some uu____2504)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2522,uu____2523);
                    FStar_Syntax_Syntax.sigrng = uu____2524;
                    FStar_Syntax_Syntax.sigquals = uu____2525;
                    FStar_Syntax_Syntax.sigmeta = uu____2526;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2545 =
                        let uu____2550 = inst_tscheme (uvs, k) in
                        (uu____2550, rng) in
                      Some uu____2545
                  | uu____2559 ->
                      let uu____2560 =
                        let uu____2565 =
                          let uu____2568 =
                            let uu____2569 =
                              let uu____2572 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2572 in
                            (uvs, uu____2569) in
                          inst_tscheme uu____2568 in
                        (uu____2565, rng) in
                      Some uu____2560)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2587,uu____2588);
                    FStar_Syntax_Syntax.sigrng = uu____2589;
                    FStar_Syntax_Syntax.sigquals = uu____2590;
                    FStar_Syntax_Syntax.sigmeta = uu____2591;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2611 =
                        let uu____2616 = inst_tscheme_with (uvs, k) us in
                        (uu____2616, rng) in
                      Some uu____2611
                  | uu____2625 ->
                      let uu____2626 =
                        let uu____2631 =
                          let uu____2634 =
                            let uu____2635 =
                              let uu____2638 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2638 in
                            (uvs, uu____2635) in
                          inst_tscheme_with uu____2634 us in
                        (uu____2631, rng) in
                      Some uu____2626)
             | FStar_Util.Inr se ->
                 let uu____2658 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2669;
                        FStar_Syntax_Syntax.sigrng = uu____2670;
                        FStar_Syntax_Syntax.sigquals = uu____2671;
                        FStar_Syntax_Syntax.sigmeta = uu____2672;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2681 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2658
                   (FStar_Util.map_option
                      (fun uu____2704  ->
                         match uu____2704 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2721 =
        let uu____2727 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2727 mapper in
      match uu____2721 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2779 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2779.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2779.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2779.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2800 = lookup_qname env l in
      match uu____2800 with | None  -> false | Some uu____2820 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2848 = try_lookup_bv env bv in
      match uu____2848 with
      | None  ->
          let uu____2856 =
            let uu____2857 =
              let uu____2860 = variable_not_found bv in (uu____2860, bvr) in
            FStar_Errors.Error uu____2857 in
          raise uu____2856
      | Some (t,r) ->
          let uu____2867 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2868 = FStar_Range.set_use_range r bvr in
          (uu____2867, uu____2868)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2880 = try_lookup_lid_aux env l in
      match uu____2880 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2922 =
            let uu____2927 =
              let uu____2930 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2930) in
            (uu____2927, r1) in
          Some uu____2922
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2947 = try_lookup_lid env l in
      match uu____2947 with
      | None  ->
          let uu____2961 =
            let uu____2962 =
              let uu____2965 = name_not_found l in
              (uu____2965, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2962 in
          raise uu____2961
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2986  ->
              match uu___103_2986 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2988 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2999 = lookup_qname env lid in
      match uu____2999 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3014,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3017;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3019;_},None
            ),uu____3020)
          ->
          let uu____3044 =
            let uu____3050 =
              let uu____3053 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____3053) in
            (uu____3050, q) in
          Some uu____3044
      | uu____3062 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3084 = lookup_qname env lid in
      match uu____3084 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3097,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3100;
              FStar_Syntax_Syntax.sigquals = uu____3101;
              FStar_Syntax_Syntax.sigmeta = uu____3102;_},None
            ),uu____3103)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3127 ->
          let uu____3138 =
            let uu____3139 =
              let uu____3142 = name_not_found lid in
              (uu____3142, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3139 in
          raise uu____3138
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3153 = lookup_qname env lid in
      match uu____3153 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3166,uvs,t,uu____3169,uu____3170,uu____3171);
              FStar_Syntax_Syntax.sigrng = uu____3172;
              FStar_Syntax_Syntax.sigquals = uu____3173;
              FStar_Syntax_Syntax.sigmeta = uu____3174;_},None
            ),uu____3175)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3201 ->
          let uu____3212 =
            let uu____3213 =
              let uu____3216 = name_not_found lid in
              (uu____3216, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3213 in
          raise uu____3212
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3228 = lookup_qname env lid in
      match uu____3228 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3242,uu____3243,uu____3244,uu____3245,uu____3246,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3248;
              FStar_Syntax_Syntax.sigquals = uu____3249;
              FStar_Syntax_Syntax.sigmeta = uu____3250;_},uu____3251),uu____3252)
          -> (true, dcs)
      | uu____3282 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3300 = lookup_qname env lid in
      match uu____3300 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3311,uu____3312,uu____3313,l,uu____3315,uu____3316);
              FStar_Syntax_Syntax.sigrng = uu____3317;
              FStar_Syntax_Syntax.sigquals = uu____3318;
              FStar_Syntax_Syntax.sigmeta = uu____3319;_},uu____3320),uu____3321)
          -> l
      | uu____3348 ->
          let uu____3359 =
            let uu____3360 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3360 in
          failwith uu____3359
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
        let uu____3384 = lookup_qname env lid in
        match uu____3384 with
        | Some (FStar_Util.Inr (se,None ),uu____3399) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3425,lbs),uu____3427,uu____3428) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3445 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3445
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3466 -> None)
        | uu____3469 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3490 = lookup_qname env ftv in
      match uu____3490 with
      | Some (FStar_Util.Inr (se,None ),uu____3503) ->
          let uu____3526 = effect_signature se in
          (match uu____3526 with
           | None  -> None
           | Some ((uu____3537,t),r) ->
               let uu____3546 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3546)
      | uu____3547 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3564 = try_lookup_effect_lid env ftv in
      match uu____3564 with
      | None  ->
          let uu____3566 =
            let uu____3567 =
              let uu____3570 = name_not_found ftv in
              (uu____3570, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3567 in
          raise uu____3566
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
        let uu____3584 = lookup_qname env lid0 in
        match uu____3584 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3602);
                FStar_Syntax_Syntax.sigrng = uu____3603;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3605;_},None
              ),uu____3606)
            ->
            let lid1 =
              let uu____3633 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3633 in
            let uu____3634 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3636  ->
                      match uu___104_3636 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3637 -> false)) in
            if uu____3634
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
                     (let uu____3659 =
                        let uu____3660 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3661 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3660 uu____3661 in
                      failwith uu____3659) in
               match (binders, univs1) with
               | ([],uu____3669) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3678,uu____3679::uu____3680::uu____3681) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3684 =
                     let uu____3685 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3686 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3685 uu____3686 in
                   failwith uu____3684
               | uu____3694 ->
                   let uu____3697 =
                     let uu____3700 =
                       let uu____3701 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3701) in
                     inst_tscheme_with uu____3700 insts in
                   (match uu____3697 with
                    | (uu____3709,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3712 =
                          let uu____3713 = FStar_Syntax_Subst.compress t1 in
                          uu____3713.FStar_Syntax_Syntax.n in
                        (match uu____3712 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3743 -> failwith "Impossible")))
        | uu____3747 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3773 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3773 with
        | None  -> None
        | Some (uu____3780,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3785 = find1 l2 in
            (match uu____3785 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3790 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3790 with
        | Some l1 -> l1
        | None  ->
            let uu____3793 = find1 l in
            (match uu____3793 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3805 = lookup_qname env l1 in
      match uu____3805 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3817;
              FStar_Syntax_Syntax.sigrng = uu____3818;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3820;_},uu____3821),uu____3822)
          -> q
      | uu____3847 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3870 =
          let uu____3871 =
            let uu____3872 = FStar_Util.string_of_int i in
            let uu____3873 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3872 uu____3873 in
          failwith uu____3871 in
        let uu____3874 = lookup_datacon env lid in
        match uu____3874 with
        | (uu____3877,t) ->
            let uu____3879 =
              let uu____3880 = FStar_Syntax_Subst.compress t in
              uu____3880.FStar_Syntax_Syntax.n in
            (match uu____3879 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3884) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3907 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3907 FStar_Pervasives.fst)
             | uu____3912 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3919 = lookup_qname env l in
      match uu____3919 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3930,uu____3931,uu____3932);
              FStar_Syntax_Syntax.sigrng = uu____3933;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3935;_},uu____3936),uu____3937)
          ->
          FStar_Util.for_some
            (fun uu___105_3962  ->
               match uu___105_3962 with
               | FStar_Syntax_Syntax.Projector uu____3963 -> true
               | uu____3966 -> false) quals
      | uu____3967 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3984 = lookup_qname env lid in
      match uu____3984 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3995,uu____3996,uu____3997,uu____3998,uu____3999,uu____4000);
              FStar_Syntax_Syntax.sigrng = uu____4001;
              FStar_Syntax_Syntax.sigquals = uu____4002;
              FStar_Syntax_Syntax.sigmeta = uu____4003;_},uu____4004),uu____4005)
          -> true
      | uu____4032 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4049 = lookup_qname env lid in
      match uu____4049 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4060,uu____4061,uu____4062,uu____4063,uu____4064,uu____4065);
              FStar_Syntax_Syntax.sigrng = uu____4066;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4068;_},uu____4069),uu____4070)
          ->
          FStar_Util.for_some
            (fun uu___106_4099  ->
               match uu___106_4099 with
               | FStar_Syntax_Syntax.RecordType uu____4100 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4105 -> true
               | uu____4110 -> false) quals
      | uu____4111 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4128 = lookup_qname env lid in
      match uu____4128 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4139,uu____4140,uu____4141);
              FStar_Syntax_Syntax.sigrng = uu____4142;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4144;_},uu____4145),uu____4146)
          ->
          FStar_Util.for_some
            (fun uu___107_4175  ->
               match uu___107_4175 with
               | FStar_Syntax_Syntax.Action uu____4176 -> true
               | uu____4177 -> false) quals
      | uu____4178 -> false
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
      let uu____4197 =
        let uu____4198 = FStar_Syntax_Util.un_uinst head1 in
        uu____4198.FStar_Syntax_Syntax.n in
      match uu____4197 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4202 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4240 -> Some false
        | FStar_Util.Inr (se,uu____4249) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4258 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4262 -> Some true
             | uu____4271 -> Some false) in
      let uu____4272 =
        let uu____4274 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4274 mapper in
      match uu____4272 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4301 = lookup_qname env lid in
      match uu____4301 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4312,uu____4313,tps,uu____4315,uu____4316,uu____4317);
              FStar_Syntax_Syntax.sigrng = uu____4318;
              FStar_Syntax_Syntax.sigquals = uu____4319;
              FStar_Syntax_Syntax.sigmeta = uu____4320;_},uu____4321),uu____4322)
          -> FStar_List.length tps
      | uu____4355 ->
          let uu____4366 =
            let uu____4367 =
              let uu____4370 = name_not_found lid in
              (uu____4370, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4367 in
          raise uu____4366
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
           (fun uu____4392  ->
              match uu____4392 with
              | (d,uu____4397) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4406 = effect_decl_opt env l in
      match uu____4406 with
      | None  ->
          let uu____4414 =
            let uu____4415 =
              let uu____4418 = name_not_found l in
              (uu____4418, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4415 in
          raise uu____4414
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
            (let uu____4461 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4485  ->
                       match uu____4485 with
                       | (m1,m2,uu____4493,uu____4494,uu____4495) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4461 with
             | None  ->
                 let uu____4504 =
                   let uu____4505 =
                     let uu____4508 =
                       let uu____4509 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4510 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4509
                         uu____4510 in
                     (uu____4508, (env.range)) in
                   FStar_Errors.Error uu____4505 in
                 raise uu____4504
             | Some (uu____4514,uu____4515,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4562 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4574  ->
            match uu____4574 with
            | (d,uu____4578) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4562 with
  | None  ->
      let uu____4585 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4585
  | Some (md,_q) ->
      let uu____4594 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4594 with
       | (uu____4601,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4609)::(wp,uu____4611)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4633 -> failwith "Impossible"))
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
                 let uu____4669 = get_range env in
                 let uu____4670 =
                   let uu____4673 =
                     let uu____4674 =
                       let uu____4684 =
                         let uu____4686 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4686] in
                       (null_wp, uu____4684) in
                     FStar_Syntax_Syntax.Tm_app uu____4674 in
                   FStar_Syntax_Syntax.mk uu____4673 in
                 uu____4670 None uu____4669 in
               let uu____4696 =
                 let uu____4697 =
                   let uu____4703 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4703] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4697;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4696)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4712 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4712.order);
              joins = (uu___118_4712.joins)
            } in
          let uu___119_4717 = env in
          {
            solver = (uu___119_4717.solver);
            range = (uu___119_4717.range);
            curmodule = (uu___119_4717.curmodule);
            gamma = (uu___119_4717.gamma);
            gamma_cache = (uu___119_4717.gamma_cache);
            modules = (uu___119_4717.modules);
            expected_typ = (uu___119_4717.expected_typ);
            sigtab = (uu___119_4717.sigtab);
            is_pattern = (uu___119_4717.is_pattern);
            instantiate_imp = (uu___119_4717.instantiate_imp);
            effects;
            generalize = (uu___119_4717.generalize);
            letrecs = (uu___119_4717.letrecs);
            top_level = (uu___119_4717.top_level);
            check_uvars = (uu___119_4717.check_uvars);
            use_eq = (uu___119_4717.use_eq);
            is_iface = (uu___119_4717.is_iface);
            admit = (uu___119_4717.admit);
            lax = (uu___119_4717.lax);
            lax_universes = (uu___119_4717.lax_universes);
            type_of = (uu___119_4717.type_of);
            universe_of = (uu___119_4717.universe_of);
            use_bv_sorts = (uu___119_4717.use_bv_sorts);
            qname_and_index = (uu___119_4717.qname_and_index);
            proof_ns = (uu___119_4717.proof_ns);
            synth = (uu___119_4717.synth)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4734 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4734 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4813 = (e1.mlift).mlift_wp t wp in
                              let uu____4814 = l1 t wp e in
                              l2 t uu____4813 uu____4814))
                | uu____4815 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4850 = inst_tscheme lift_t in
            match uu____4850 with
            | (uu____4855,lift_t1) ->
                let uu____4857 =
                  let uu____4860 =
                    let uu____4861 =
                      let uu____4871 =
                        let uu____4873 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4874 =
                          let uu____4876 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4876] in
                        uu____4873 :: uu____4874 in
                      (lift_t1, uu____4871) in
                    FStar_Syntax_Syntax.Tm_app uu____4861 in
                  FStar_Syntax_Syntax.mk uu____4860 in
                uu____4857 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4921 = inst_tscheme lift_t in
            match uu____4921 with
            | (uu____4926,lift_t1) ->
                let uu____4928 =
                  let uu____4931 =
                    let uu____4932 =
                      let uu____4942 =
                        let uu____4944 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4945 =
                          let uu____4947 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4948 =
                            let uu____4950 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4950] in
                          uu____4947 :: uu____4948 in
                        uu____4944 :: uu____4945 in
                      (lift_t1, uu____4942) in
                    FStar_Syntax_Syntax.Tm_app uu____4932 in
                  FStar_Syntax_Syntax.mk uu____4931 in
                uu____4928 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4991 =
                let uu____4992 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4992
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4991 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4996 =
              let uu____4997 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4997 in
            let uu____4998 =
              let uu____4999 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____5014 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____5014) in
              FStar_Util.dflt "none" uu____4999 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4996
              uu____4998 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____5027  ->
                    match uu____5027 with
                    | (e,uu____5032) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____5045 =
            match uu____5045 with
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
              let uu____5070 =
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
                                    (let uu____5082 =
                                       let uu____5087 =
                                         find_edge order1 (i, k) in
                                       let uu____5089 =
                                         find_edge order1 (k, j) in
                                       (uu____5087, uu____5089) in
                                     match uu____5082 with
                                     | (Some e1,Some e2) ->
                                         let uu____5098 = compose_edges e1 e2 in
                                         [uu____5098]
                                     | uu____5099 -> []))))) in
              FStar_List.append order1 uu____5070 in
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
                   let uu____5114 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5115 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5115
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5114
                   then
                     let uu____5118 =
                       let uu____5119 =
                         let uu____5122 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5123 = get_range env in
                         (uu____5122, uu____5123) in
                       FStar_Errors.Error uu____5119 in
                     raise uu____5118
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
                                            let uu____5186 =
                                              let uu____5191 =
                                                find_edge order2 (i, k) in
                                              let uu____5193 =
                                                find_edge order2 (j, k) in
                                              (uu____5191, uu____5193) in
                                            match uu____5186 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5216,uu____5217)
                                                     ->
                                                     let uu____5221 =
                                                       let uu____5224 =
                                                         let uu____5225 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5225 in
                                                       let uu____5227 =
                                                         let uu____5228 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5228 in
                                                       (uu____5224,
                                                         uu____5227) in
                                                     (match uu____5221 with
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
                                            | uu____5247 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5286 = env.effects in
              { decls = (uu___120_5286.decls); order = order2; joins } in
            let uu___121_5287 = env in
            {
              solver = (uu___121_5287.solver);
              range = (uu___121_5287.range);
              curmodule = (uu___121_5287.curmodule);
              gamma = (uu___121_5287.gamma);
              gamma_cache = (uu___121_5287.gamma_cache);
              modules = (uu___121_5287.modules);
              expected_typ = (uu___121_5287.expected_typ);
              sigtab = (uu___121_5287.sigtab);
              is_pattern = (uu___121_5287.is_pattern);
              instantiate_imp = (uu___121_5287.instantiate_imp);
              effects;
              generalize = (uu___121_5287.generalize);
              letrecs = (uu___121_5287.letrecs);
              top_level = (uu___121_5287.top_level);
              check_uvars = (uu___121_5287.check_uvars);
              use_eq = (uu___121_5287.use_eq);
              is_iface = (uu___121_5287.is_iface);
              admit = (uu___121_5287.admit);
              lax = (uu___121_5287.lax);
              lax_universes = (uu___121_5287.lax_universes);
              type_of = (uu___121_5287.type_of);
              universe_of = (uu___121_5287.universe_of);
              use_bv_sorts = (uu___121_5287.use_bv_sorts);
              qname_and_index = (uu___121_5287.qname_and_index);
              proof_ns = (uu___121_5287.proof_ns);
              synth = (uu___121_5287.synth)
            }))
      | uu____5288 -> env
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
        | uu____5310 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5318 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5318 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5328 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5328 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5350 =
                     let uu____5351 =
                       let uu____5354 =
                         let uu____5355 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5364 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5375 =
                           let uu____5376 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5376 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5355 uu____5364 uu____5375 in
                       (uu____5354, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5351 in
                   raise uu____5350)
                else ();
                (let inst1 =
                   let uu____5380 =
                     let uu____5386 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5386 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5393  ->
                        fun uu____5394  ->
                          match (uu____5393, uu____5394) with
                          | ((x,uu____5408),(t,uu____5410)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5380 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5425 =
                     let uu___122_5426 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5426.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5426.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5426.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5426.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5425
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5456 =
    let uu____5461 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5461 in
  match uu____5456 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5477 =
        only_reifiable &&
          (let uu____5478 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5478) in
      if uu____5477
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5491 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5493 =
               let uu____5502 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5502) in
             (match uu____5493 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5536 =
                    let uu____5539 = get_range env in
                    let uu____5540 =
                      let uu____5543 =
                        let uu____5544 =
                          let uu____5554 =
                            let uu____5556 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5556; wp] in
                          (repr, uu____5554) in
                        FStar_Syntax_Syntax.Tm_app uu____5544 in
                      FStar_Syntax_Syntax.mk uu____5543 in
                    uu____5540 None uu____5539 in
                  Some uu____5536))
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
          let uu____5600 =
            let uu____5601 =
              let uu____5604 =
                let uu____5605 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5605 in
              let uu____5606 = get_range env in (uu____5604, uu____5606) in
            FStar_Errors.Error uu____5601 in
          raise uu____5600 in
        let uu____5607 = effect_repr_aux true env c u_c in
        match uu____5607 with
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
        | FStar_Util.Inr (eff_name,uu____5639) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5652 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5659 =
        let uu____5660 = FStar_Syntax_Subst.compress t in
        uu____5660.FStar_Syntax_Syntax.n in
      match uu____5659 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5663,c) ->
          is_reifiable_comp env c
      | uu____5675 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5693)::uu____5694 -> x :: rest
        | (Binding_sig_inst uu____5699)::uu____5700 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5709 = push1 x rest1 in local :: uu____5709 in
      let uu___123_5711 = env in
      let uu____5712 = push1 s env.gamma in
      {
        solver = (uu___123_5711.solver);
        range = (uu___123_5711.range);
        curmodule = (uu___123_5711.curmodule);
        gamma = uu____5712;
        gamma_cache = (uu___123_5711.gamma_cache);
        modules = (uu___123_5711.modules);
        expected_typ = (uu___123_5711.expected_typ);
        sigtab = (uu___123_5711.sigtab);
        is_pattern = (uu___123_5711.is_pattern);
        instantiate_imp = (uu___123_5711.instantiate_imp);
        effects = (uu___123_5711.effects);
        generalize = (uu___123_5711.generalize);
        letrecs = (uu___123_5711.letrecs);
        top_level = (uu___123_5711.top_level);
        check_uvars = (uu___123_5711.check_uvars);
        use_eq = (uu___123_5711.use_eq);
        is_iface = (uu___123_5711.is_iface);
        admit = (uu___123_5711.admit);
        lax = (uu___123_5711.lax);
        lax_universes = (uu___123_5711.lax_universes);
        type_of = (uu___123_5711.type_of);
        universe_of = (uu___123_5711.universe_of);
        use_bv_sorts = (uu___123_5711.use_bv_sorts);
        qname_and_index = (uu___123_5711.qname_and_index);
        proof_ns = (uu___123_5711.proof_ns);
        synth = (uu___123_5711.synth)
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
      let uu___124_5739 = env in
      {
        solver = (uu___124_5739.solver);
        range = (uu___124_5739.range);
        curmodule = (uu___124_5739.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5739.gamma_cache);
        modules = (uu___124_5739.modules);
        expected_typ = (uu___124_5739.expected_typ);
        sigtab = (uu___124_5739.sigtab);
        is_pattern = (uu___124_5739.is_pattern);
        instantiate_imp = (uu___124_5739.instantiate_imp);
        effects = (uu___124_5739.effects);
        generalize = (uu___124_5739.generalize);
        letrecs = (uu___124_5739.letrecs);
        top_level = (uu___124_5739.top_level);
        check_uvars = (uu___124_5739.check_uvars);
        use_eq = (uu___124_5739.use_eq);
        is_iface = (uu___124_5739.is_iface);
        admit = (uu___124_5739.admit);
        lax = (uu___124_5739.lax);
        lax_universes = (uu___124_5739.lax_universes);
        type_of = (uu___124_5739.type_of);
        universe_of = (uu___124_5739.universe_of);
        use_bv_sorts = (uu___124_5739.use_bv_sorts);
        qname_and_index = (uu___124_5739.qname_and_index);
        proof_ns = (uu___124_5739.proof_ns);
        synth = (uu___124_5739.synth)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5760 = env in
             {
               solver = (uu___125_5760.solver);
               range = (uu___125_5760.range);
               curmodule = (uu___125_5760.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5760.gamma_cache);
               modules = (uu___125_5760.modules);
               expected_typ = (uu___125_5760.expected_typ);
               sigtab = (uu___125_5760.sigtab);
               is_pattern = (uu___125_5760.is_pattern);
               instantiate_imp = (uu___125_5760.instantiate_imp);
               effects = (uu___125_5760.effects);
               generalize = (uu___125_5760.generalize);
               letrecs = (uu___125_5760.letrecs);
               top_level = (uu___125_5760.top_level);
               check_uvars = (uu___125_5760.check_uvars);
               use_eq = (uu___125_5760.use_eq);
               is_iface = (uu___125_5760.is_iface);
               admit = (uu___125_5760.admit);
               lax = (uu___125_5760.lax);
               lax_universes = (uu___125_5760.lax_universes);
               type_of = (uu___125_5760.type_of);
               universe_of = (uu___125_5760.universe_of);
               use_bv_sorts = (uu___125_5760.use_bv_sorts);
               qname_and_index = (uu___125_5760.qname_and_index);
               proof_ns = (uu___125_5760.proof_ns);
               synth = (uu___125_5760.synth)
             }))
    | uu____5761 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5774  ->
             match uu____5774 with | (x,uu____5778) -> push_bv env1 x) env bs
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
            let uu___126_5798 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5798.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5798.FStar_Syntax_Syntax.index);
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
      (let uu___127_5828 = env in
       {
         solver = (uu___127_5828.solver);
         range = (uu___127_5828.range);
         curmodule = (uu___127_5828.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5828.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5828.sigtab);
         is_pattern = (uu___127_5828.is_pattern);
         instantiate_imp = (uu___127_5828.instantiate_imp);
         effects = (uu___127_5828.effects);
         generalize = (uu___127_5828.generalize);
         letrecs = (uu___127_5828.letrecs);
         top_level = (uu___127_5828.top_level);
         check_uvars = (uu___127_5828.check_uvars);
         use_eq = (uu___127_5828.use_eq);
         is_iface = (uu___127_5828.is_iface);
         admit = (uu___127_5828.admit);
         lax = (uu___127_5828.lax);
         lax_universes = (uu___127_5828.lax_universes);
         type_of = (uu___127_5828.type_of);
         universe_of = (uu___127_5828.universe_of);
         use_bv_sorts = (uu___127_5828.use_bv_sorts);
         qname_and_index = (uu___127_5828.qname_and_index);
         proof_ns = (uu___127_5828.proof_ns);
         synth = (uu___127_5828.synth)
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
        let uu____5852 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5852 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5868 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5868)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5878 = env in
      {
        solver = (uu___128_5878.solver);
        range = (uu___128_5878.range);
        curmodule = (uu___128_5878.curmodule);
        gamma = (uu___128_5878.gamma);
        gamma_cache = (uu___128_5878.gamma_cache);
        modules = (uu___128_5878.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5878.sigtab);
        is_pattern = (uu___128_5878.is_pattern);
        instantiate_imp = (uu___128_5878.instantiate_imp);
        effects = (uu___128_5878.effects);
        generalize = (uu___128_5878.generalize);
        letrecs = (uu___128_5878.letrecs);
        top_level = (uu___128_5878.top_level);
        check_uvars = (uu___128_5878.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5878.is_iface);
        admit = (uu___128_5878.admit);
        lax = (uu___128_5878.lax);
        lax_universes = (uu___128_5878.lax_universes);
        type_of = (uu___128_5878.type_of);
        universe_of = (uu___128_5878.universe_of);
        use_bv_sorts = (uu___128_5878.use_bv_sorts);
        qname_and_index = (uu___128_5878.qname_and_index);
        proof_ns = (uu___128_5878.proof_ns);
        synth = (uu___128_5878.synth)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5894 = expected_typ env_ in
    ((let uu___129_5897 = env_ in
      {
        solver = (uu___129_5897.solver);
        range = (uu___129_5897.range);
        curmodule = (uu___129_5897.curmodule);
        gamma = (uu___129_5897.gamma);
        gamma_cache = (uu___129_5897.gamma_cache);
        modules = (uu___129_5897.modules);
        expected_typ = None;
        sigtab = (uu___129_5897.sigtab);
        is_pattern = (uu___129_5897.is_pattern);
        instantiate_imp = (uu___129_5897.instantiate_imp);
        effects = (uu___129_5897.effects);
        generalize = (uu___129_5897.generalize);
        letrecs = (uu___129_5897.letrecs);
        top_level = (uu___129_5897.top_level);
        check_uvars = (uu___129_5897.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5897.is_iface);
        admit = (uu___129_5897.admit);
        lax = (uu___129_5897.lax);
        lax_universes = (uu___129_5897.lax_universes);
        type_of = (uu___129_5897.type_of);
        universe_of = (uu___129_5897.universe_of);
        use_bv_sorts = (uu___129_5897.use_bv_sorts);
        qname_and_index = (uu___129_5897.qname_and_index);
        proof_ns = (uu___129_5897.proof_ns);
        synth = (uu___129_5897.synth)
      }), uu____5894)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5908 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5912  ->
                    match uu___108_5912 with
                    | Binding_sig (uu____5914,se) -> [se]
                    | uu____5918 -> [])) in
          FStar_All.pipe_right uu____5908 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5923 = env in
       {
         solver = (uu___130_5923.solver);
         range = (uu___130_5923.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5923.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5923.expected_typ);
         sigtab = (uu___130_5923.sigtab);
         is_pattern = (uu___130_5923.is_pattern);
         instantiate_imp = (uu___130_5923.instantiate_imp);
         effects = (uu___130_5923.effects);
         generalize = (uu___130_5923.generalize);
         letrecs = (uu___130_5923.letrecs);
         top_level = (uu___130_5923.top_level);
         check_uvars = (uu___130_5923.check_uvars);
         use_eq = (uu___130_5923.use_eq);
         is_iface = (uu___130_5923.is_iface);
         admit = (uu___130_5923.admit);
         lax = (uu___130_5923.lax);
         lax_universes = (uu___130_5923.lax_universes);
         type_of = (uu___130_5923.type_of);
         universe_of = (uu___130_5923.universe_of);
         use_bv_sorts = (uu___130_5923.use_bv_sorts);
         qname_and_index = (uu___130_5923.qname_and_index);
         proof_ns = (uu___130_5923.proof_ns);
         synth = (uu___130_5923.synth)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5973)::tl1 -> aux out tl1
      | (Binding_lid (uu____5976,(uu____5977,t)))::tl1 ->
          let uu____5986 =
            let uu____5990 = FStar_Syntax_Free.uvars t in ext out uu____5990 in
          aux uu____5986 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5994;
            FStar_Syntax_Syntax.index = uu____5995;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6001 =
            let uu____6005 = FStar_Syntax_Free.uvars t in ext out uu____6005 in
          aux uu____6001 tl1
      | (Binding_sig uu____6009)::uu____6010 -> out
      | (Binding_sig_inst uu____6015)::uu____6016 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6053)::tl1 -> aux out tl1
      | (Binding_univ uu____6060)::tl1 -> aux out tl1
      | (Binding_lid (uu____6063,(uu____6064,t)))::tl1 ->
          let uu____6073 =
            let uu____6075 = FStar_Syntax_Free.univs t in ext out uu____6075 in
          aux uu____6073 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6077;
            FStar_Syntax_Syntax.index = uu____6078;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6084 =
            let uu____6086 = FStar_Syntax_Free.univs t in ext out uu____6086 in
          aux uu____6084 tl1
      | (Binding_sig uu____6088)::uu____6089 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6126)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6136 = FStar_Util.set_add uname out in aux uu____6136 tl1
      | (Binding_lid (uu____6138,(uu____6139,t)))::tl1 ->
          let uu____6148 =
            let uu____6150 = FStar_Syntax_Free.univnames t in
            ext out uu____6150 in
          aux uu____6148 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6152;
            FStar_Syntax_Syntax.index = uu____6153;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6159 =
            let uu____6161 = FStar_Syntax_Free.univnames t in
            ext out uu____6161 in
          aux uu____6159 tl1
      | (Binding_sig uu____6163)::uu____6164 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6180  ->
            match uu___109_6180 with
            | Binding_var x -> [x]
            | Binding_lid uu____6183 -> []
            | Binding_sig uu____6186 -> []
            | Binding_univ uu____6190 -> []
            | Binding_sig_inst uu____6191 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6201 =
      let uu____6203 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6203
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6201 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6219 =
      let uu____6220 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6224  ->
                match uu___110_6224 with
                | Binding_var x ->
                    let uu____6226 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6226
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6229) ->
                    let uu____6230 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6230
                | Binding_sig (ls,uu____6232) ->
                    let uu____6235 =
                      let uu____6236 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6236
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6235
                | Binding_sig_inst (ls,uu____6242,uu____6243) ->
                    let uu____6246 =
                      let uu____6247 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6247
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6246)) in
      FStar_All.pipe_right uu____6220 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6219 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6259 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6259
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6280  ->
                 fun uu____6281  ->
                   match (uu____6280, uu____6281) with
                   | ((b1,uu____6291),(b2,uu____6293)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6336  ->
             match uu___111_6336 with
             | Binding_sig (lids,uu____6340) -> FStar_List.append lids keys
             | uu____6343 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6345  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6370) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6382,uu____6383) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6407 = list_prefix p path1 in
            if uu____6407 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6417 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6417
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6437 = e in
            {
              solver = (uu___131_6437.solver);
              range = (uu___131_6437.range);
              curmodule = (uu___131_6437.curmodule);
              gamma = (uu___131_6437.gamma);
              gamma_cache = (uu___131_6437.gamma_cache);
              modules = (uu___131_6437.modules);
              expected_typ = (uu___131_6437.expected_typ);
              sigtab = (uu___131_6437.sigtab);
              is_pattern = (uu___131_6437.is_pattern);
              instantiate_imp = (uu___131_6437.instantiate_imp);
              effects = (uu___131_6437.effects);
              generalize = (uu___131_6437.generalize);
              letrecs = (uu___131_6437.letrecs);
              top_level = (uu___131_6437.top_level);
              check_uvars = (uu___131_6437.check_uvars);
              use_eq = (uu___131_6437.use_eq);
              is_iface = (uu___131_6437.is_iface);
              admit = (uu___131_6437.admit);
              lax = (uu___131_6437.lax);
              lax_universes = (uu___131_6437.lax_universes);
              type_of = (uu___131_6437.type_of);
              universe_of = (uu___131_6437.universe_of);
              use_bv_sorts = (uu___131_6437.use_bv_sorts);
              qname_and_index = (uu___131_6437.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_6437.synth)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6456 = e in
    {
      solver = (uu___132_6456.solver);
      range = (uu___132_6456.range);
      curmodule = (uu___132_6456.curmodule);
      gamma = (uu___132_6456.gamma);
      gamma_cache = (uu___132_6456.gamma_cache);
      modules = (uu___132_6456.modules);
      expected_typ = (uu___132_6456.expected_typ);
      sigtab = (uu___132_6456.sigtab);
      is_pattern = (uu___132_6456.is_pattern);
      instantiate_imp = (uu___132_6456.instantiate_imp);
      effects = (uu___132_6456.effects);
      generalize = (uu___132_6456.generalize);
      letrecs = (uu___132_6456.letrecs);
      top_level = (uu___132_6456.top_level);
      check_uvars = (uu___132_6456.check_uvars);
      use_eq = (uu___132_6456.use_eq);
      is_iface = (uu___132_6456.is_iface);
      admit = (uu___132_6456.admit);
      lax = (uu___132_6456.lax);
      lax_universes = (uu___132_6456.lax_universes);
      type_of = (uu___132_6456.type_of);
      universe_of = (uu___132_6456.universe_of);
      use_bv_sorts = (uu___132_6456.use_bv_sorts);
      qname_and_index = (uu___132_6456.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_6456.synth)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6465::rest ->
        let uu___133_6468 = e in
        {
          solver = (uu___133_6468.solver);
          range = (uu___133_6468.range);
          curmodule = (uu___133_6468.curmodule);
          gamma = (uu___133_6468.gamma);
          gamma_cache = (uu___133_6468.gamma_cache);
          modules = (uu___133_6468.modules);
          expected_typ = (uu___133_6468.expected_typ);
          sigtab = (uu___133_6468.sigtab);
          is_pattern = (uu___133_6468.is_pattern);
          instantiate_imp = (uu___133_6468.instantiate_imp);
          effects = (uu___133_6468.effects);
          generalize = (uu___133_6468.generalize);
          letrecs = (uu___133_6468.letrecs);
          top_level = (uu___133_6468.top_level);
          check_uvars = (uu___133_6468.check_uvars);
          use_eq = (uu___133_6468.use_eq);
          is_iface = (uu___133_6468.is_iface);
          admit = (uu___133_6468.admit);
          lax = (uu___133_6468.lax);
          lax_universes = (uu___133_6468.lax_universes);
          type_of = (uu___133_6468.type_of);
          universe_of = (uu___133_6468.universe_of);
          use_bv_sorts = (uu___133_6468.use_bv_sorts);
          qname_and_index = (uu___133_6468.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_6468.synth)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6478 = e in
      {
        solver = (uu___134_6478.solver);
        range = (uu___134_6478.range);
        curmodule = (uu___134_6478.curmodule);
        gamma = (uu___134_6478.gamma);
        gamma_cache = (uu___134_6478.gamma_cache);
        modules = (uu___134_6478.modules);
        expected_typ = (uu___134_6478.expected_typ);
        sigtab = (uu___134_6478.sigtab);
        is_pattern = (uu___134_6478.is_pattern);
        instantiate_imp = (uu___134_6478.instantiate_imp);
        effects = (uu___134_6478.effects);
        generalize = (uu___134_6478.generalize);
        letrecs = (uu___134_6478.letrecs);
        top_level = (uu___134_6478.top_level);
        check_uvars = (uu___134_6478.check_uvars);
        use_eq = (uu___134_6478.use_eq);
        is_iface = (uu___134_6478.is_iface);
        admit = (uu___134_6478.admit);
        lax = (uu___134_6478.lax);
        lax_universes = (uu___134_6478.lax_universes);
        type_of = (uu___134_6478.type_of);
        universe_of = (uu___134_6478.universe_of);
        use_bv_sorts = (uu___134_6478.use_bv_sorts);
        qname_and_index = (uu___134_6478.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_6478.synth)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6496 =
        FStar_List.map
          (fun fpns  ->
             let uu____6507 =
               let uu____6508 =
                 let uu____6509 =
                   FStar_List.map
                     (fun uu____6514  ->
                        match uu____6514 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6509 in
               Prims.strcat uu____6508 "]" in
             Prims.strcat "[" uu____6507) pns in
      FStar_String.concat ";" uu____6496 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6523  -> ());
    push = (fun uu____6524  -> ());
    pop = (fun uu____6525  -> ());
    mark = (fun uu____6526  -> ());
    reset_mark = (fun uu____6527  -> ());
    commit_mark = (fun uu____6528  -> ());
    encode_modul = (fun uu____6529  -> fun uu____6530  -> ());
    encode_sig = (fun uu____6531  -> fun uu____6532  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6539  -> fun uu____6540  -> fun uu____6541  -> ());
    is_trivial = (fun uu____6545  -> fun uu____6546  -> false);
    finish = (fun uu____6547  -> ());
    refresh = (fun uu____6548  -> ())
  }