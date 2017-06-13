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
                   (let uu____3654 =
                      let uu____3655 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3656 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3655 uu____3656 in
                    failwith uu____3654) in
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
               | uu____3689 ->
                   let uu____3692 =
                     let uu____3695 =
                       let uu____3696 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3696) in
                     inst_tscheme_with uu____3695 insts in
                   (match uu____3692 with
                    | (uu____3704,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3707 =
                          let uu____3708 = FStar_Syntax_Subst.compress t1 in
                          uu____3708.FStar_Syntax_Syntax.n in
                        (match uu____3707 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3738 -> failwith "Impossible")))
        | uu____3742 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3768 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3768 with
        | None  -> None
        | Some (uu____3775,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3780 = find1 l2 in
            (match uu____3780 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3785 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3785 with
        | Some l1 -> l1
        | None  ->
            let uu____3788 = find1 l in
            (match uu____3788 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3800 = lookup_qname env l1 in
      match uu____3800 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3812;
              FStar_Syntax_Syntax.sigrng = uu____3813;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3815;_},uu____3816),uu____3817)
          -> q
      | uu____3842 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3865 =
          let uu____3866 =
            let uu____3867 = FStar_Util.string_of_int i in
            let uu____3868 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3867 uu____3868 in
          failwith uu____3866 in
        let uu____3869 = lookup_datacon env lid in
        match uu____3869 with
        | (uu____3872,t) ->
            let uu____3874 =
              let uu____3875 = FStar_Syntax_Subst.compress t in
              uu____3875.FStar_Syntax_Syntax.n in
            (match uu____3874 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3879) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3902 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3902 FStar_Pervasives.fst)
             | uu____3907 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3914 = lookup_qname env l in
      match uu____3914 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3925,uu____3926,uu____3927);
              FStar_Syntax_Syntax.sigrng = uu____3928;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3930;_},uu____3931),uu____3932)
          ->
          FStar_Util.for_some
            (fun uu___105_3957  ->
               match uu___105_3957 with
               | FStar_Syntax_Syntax.Projector uu____3958 -> true
               | uu____3961 -> false) quals
      | uu____3962 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3979 = lookup_qname env lid in
      match uu____3979 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3990,uu____3991,uu____3992,uu____3993,uu____3994,uu____3995);
              FStar_Syntax_Syntax.sigrng = uu____3996;
              FStar_Syntax_Syntax.sigquals = uu____3997;
              FStar_Syntax_Syntax.sigmeta = uu____3998;_},uu____3999),uu____4000)
          -> true
      | uu____4027 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4044 = lookup_qname env lid in
      match uu____4044 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4055,uu____4056,uu____4057,uu____4058,uu____4059,uu____4060);
              FStar_Syntax_Syntax.sigrng = uu____4061;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4063;_},uu____4064),uu____4065)
          ->
          FStar_Util.for_some
            (fun uu___106_4094  ->
               match uu___106_4094 with
               | FStar_Syntax_Syntax.RecordType uu____4095 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4100 -> true
               | uu____4105 -> false) quals
      | uu____4106 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4123 = lookup_qname env lid in
      match uu____4123 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4134,uu____4135,uu____4136);
              FStar_Syntax_Syntax.sigrng = uu____4137;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4139;_},uu____4140),uu____4141)
          ->
          FStar_Util.for_some
            (fun uu___107_4170  ->
               match uu___107_4170 with
               | FStar_Syntax_Syntax.Action uu____4171 -> true
               | uu____4172 -> false) quals
      | uu____4173 -> false
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
      let uu____4192 =
        let uu____4193 = FStar_Syntax_Util.un_uinst head1 in
        uu____4193.FStar_Syntax_Syntax.n in
      match uu____4192 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4197 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4235 -> Some false
        | FStar_Util.Inr (se,uu____4244) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4253 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4257 -> Some true
             | uu____4266 -> Some false) in
      let uu____4267 =
        let uu____4269 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4269 mapper in
      match uu____4267 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4296 = lookup_qname env lid in
      match uu____4296 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4307,uu____4308,tps,uu____4310,uu____4311,uu____4312);
              FStar_Syntax_Syntax.sigrng = uu____4313;
              FStar_Syntax_Syntax.sigquals = uu____4314;
              FStar_Syntax_Syntax.sigmeta = uu____4315;_},uu____4316),uu____4317)
          -> FStar_List.length tps
      | uu____4350 ->
          let uu____4361 =
            let uu____4362 =
              let uu____4365 = name_not_found lid in
              (uu____4365, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4362 in
          raise uu____4361
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
           (fun uu____4387  ->
              match uu____4387 with
              | (d,uu____4392) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4401 = effect_decl_opt env l in
      match uu____4401 with
      | None  ->
          let uu____4409 =
            let uu____4410 =
              let uu____4413 = name_not_found l in
              (uu____4413, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4410 in
          raise uu____4409
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
            (let uu____4456 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4480  ->
                       match uu____4480 with
                       | (m1,m2,uu____4488,uu____4489,uu____4490) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4456 with
             | None  ->
                 let uu____4499 =
                   let uu____4500 =
                     let uu____4503 =
                       let uu____4504 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4505 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4504
                         uu____4505 in
                     (uu____4503, (env.range)) in
                   FStar_Errors.Error uu____4500 in
                 raise uu____4499
             | Some (uu____4509,uu____4510,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4557 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4569  ->
            match uu____4569 with
            | (d,uu____4573) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4557 with
  | None  ->
      let uu____4580 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4580
  | Some (md,_q) ->
      let uu____4589 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4589 with
       | (uu____4596,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4604)::(wp,uu____4606)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4628 -> failwith "Impossible"))
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
                 let uu____4664 = get_range env in
                 let uu____4665 =
                   let uu____4668 =
                     let uu____4669 =
                       let uu____4679 =
                         let uu____4681 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4681] in
                       (null_wp, uu____4679) in
                     FStar_Syntax_Syntax.Tm_app uu____4669 in
                   FStar_Syntax_Syntax.mk uu____4668 in
                 uu____4665 None uu____4664 in
               let uu____4691 =
                 let uu____4692 =
                   let uu____4698 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4698] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4692;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4691)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4707 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4707.order);
              joins = (uu___118_4707.joins)
            } in
          let uu___119_4712 = env in
          {
            solver = (uu___119_4712.solver);
            range = (uu___119_4712.range);
            curmodule = (uu___119_4712.curmodule);
            gamma = (uu___119_4712.gamma);
            gamma_cache = (uu___119_4712.gamma_cache);
            modules = (uu___119_4712.modules);
            expected_typ = (uu___119_4712.expected_typ);
            sigtab = (uu___119_4712.sigtab);
            is_pattern = (uu___119_4712.is_pattern);
            instantiate_imp = (uu___119_4712.instantiate_imp);
            effects;
            generalize = (uu___119_4712.generalize);
            letrecs = (uu___119_4712.letrecs);
            top_level = (uu___119_4712.top_level);
            check_uvars = (uu___119_4712.check_uvars);
            use_eq = (uu___119_4712.use_eq);
            is_iface = (uu___119_4712.is_iface);
            admit = (uu___119_4712.admit);
            lax = (uu___119_4712.lax);
            lax_universes = (uu___119_4712.lax_universes);
            type_of = (uu___119_4712.type_of);
            universe_of = (uu___119_4712.universe_of);
            use_bv_sorts = (uu___119_4712.use_bv_sorts);
            qname_and_index = (uu___119_4712.qname_and_index);
            proof_ns = (uu___119_4712.proof_ns);
            synth = (uu___119_4712.synth)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4729 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4729 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4808 = (e1.mlift).mlift_wp t wp in
                              let uu____4809 = l1 t wp e in
                              l2 t uu____4808 uu____4809))
                | uu____4810 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4845 = inst_tscheme lift_t in
            match uu____4845 with
            | (uu____4850,lift_t1) ->
                let uu____4852 =
                  let uu____4855 =
                    let uu____4856 =
                      let uu____4866 =
                        let uu____4868 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4869 =
                          let uu____4871 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4871] in
                        uu____4868 :: uu____4869 in
                      (lift_t1, uu____4866) in
                    FStar_Syntax_Syntax.Tm_app uu____4856 in
                  FStar_Syntax_Syntax.mk uu____4855 in
                uu____4852 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4916 = inst_tscheme lift_t in
            match uu____4916 with
            | (uu____4921,lift_t1) ->
                let uu____4923 =
                  let uu____4926 =
                    let uu____4927 =
                      let uu____4937 =
                        let uu____4939 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4940 =
                          let uu____4942 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4943 =
                            let uu____4945 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4945] in
                          uu____4942 :: uu____4943 in
                        uu____4939 :: uu____4940 in
                      (lift_t1, uu____4937) in
                    FStar_Syntax_Syntax.Tm_app uu____4927 in
                  FStar_Syntax_Syntax.mk uu____4926 in
                uu____4923 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4986 =
                let uu____4987 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4987
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4986 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4991 =
              let uu____4992 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4992 in
            let uu____4993 =
              let uu____4994 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____5009 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____5009) in
              FStar_Util.dflt "none" uu____4994 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4991
              uu____4993 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____5022  ->
                    match uu____5022 with
                    | (e,uu____5027) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____5040 =
            match uu____5040 with
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
              let uu____5065 =
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
                                    (let uu____5077 =
                                       let uu____5082 =
                                         find_edge order1 (i, k) in
                                       let uu____5084 =
                                         find_edge order1 (k, j) in
                                       (uu____5082, uu____5084) in
                                     match uu____5077 with
                                     | (Some e1,Some e2) ->
                                         let uu____5093 = compose_edges e1 e2 in
                                         [uu____5093]
                                     | uu____5094 -> []))))) in
              FStar_List.append order1 uu____5065 in
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
                   let uu____5109 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5110 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____5110
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____5109
                   then
                     let uu____5113 =
                       let uu____5114 =
                         let uu____5117 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5118 = get_range env in
                         (uu____5117, uu____5118) in
                       FStar_Errors.Error uu____5114 in
                     raise uu____5113
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
                                            let uu____5181 =
                                              let uu____5186 =
                                                find_edge order2 (i, k) in
                                              let uu____5188 =
                                                find_edge order2 (j, k) in
                                              (uu____5186, uu____5188) in
                                            match uu____5181 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5211,uu____5212)
                                                     ->
                                                     let uu____5216 =
                                                       let uu____5219 =
                                                         let uu____5220 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5220 in
                                                       let uu____5222 =
                                                         let uu____5223 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5223 in
                                                       (uu____5219,
                                                         uu____5222) in
                                                     (match uu____5216 with
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
                                            | uu____5242 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5281 = env.effects in
              { decls = (uu___120_5281.decls); order = order2; joins } in
            let uu___121_5282 = env in
            {
              solver = (uu___121_5282.solver);
              range = (uu___121_5282.range);
              curmodule = (uu___121_5282.curmodule);
              gamma = (uu___121_5282.gamma);
              gamma_cache = (uu___121_5282.gamma_cache);
              modules = (uu___121_5282.modules);
              expected_typ = (uu___121_5282.expected_typ);
              sigtab = (uu___121_5282.sigtab);
              is_pattern = (uu___121_5282.is_pattern);
              instantiate_imp = (uu___121_5282.instantiate_imp);
              effects;
              generalize = (uu___121_5282.generalize);
              letrecs = (uu___121_5282.letrecs);
              top_level = (uu___121_5282.top_level);
              check_uvars = (uu___121_5282.check_uvars);
              use_eq = (uu___121_5282.use_eq);
              is_iface = (uu___121_5282.is_iface);
              admit = (uu___121_5282.admit);
              lax = (uu___121_5282.lax);
              lax_universes = (uu___121_5282.lax_universes);
              type_of = (uu___121_5282.type_of);
              universe_of = (uu___121_5282.universe_of);
              use_bv_sorts = (uu___121_5282.use_bv_sorts);
              qname_and_index = (uu___121_5282.qname_and_index);
              proof_ns = (uu___121_5282.proof_ns);
              synth = (uu___121_5282.synth)
            }))
      | uu____5283 -> env
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
        | uu____5305 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5313 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5313 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5323 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5323 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5345 =
                     let uu____5346 =
                       let uu____5349 =
                         let uu____5350 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5359 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5370 =
                           let uu____5371 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5371 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5350 uu____5359 uu____5370 in
                       (uu____5349, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5346 in
                   raise uu____5345)
                else ();
                (let inst1 =
                   let uu____5375 =
                     let uu____5381 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5381 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5388  ->
                        fun uu____5389  ->
                          match (uu____5388, uu____5389) with
                          | ((x,uu____5403),(t,uu____5405)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5375 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5420 =
                     let uu___122_5421 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5421.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5421.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5421.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5421.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5420
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5451 =
    let uu____5456 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5456 in
  match uu____5451 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5472 =
        only_reifiable &&
          (let uu____5473 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5473) in
      if uu____5472
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5486 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5488 =
               let uu____5497 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5497) in
             (match uu____5488 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5531 =
                    let uu____5534 = get_range env in
                    let uu____5535 =
                      let uu____5538 =
                        let uu____5539 =
                          let uu____5549 =
                            let uu____5551 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5551; wp] in
                          (repr, uu____5549) in
                        FStar_Syntax_Syntax.Tm_app uu____5539 in
                      FStar_Syntax_Syntax.mk uu____5538 in
                    uu____5535 None uu____5534 in
                  Some uu____5531))
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
          let uu____5595 =
            let uu____5596 =
              let uu____5599 =
                let uu____5600 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5600 in
              let uu____5601 = get_range env in (uu____5599, uu____5601) in
            FStar_Errors.Error uu____5596 in
          raise uu____5595 in
        let uu____5602 = effect_repr_aux true env c u_c in
        match uu____5602 with
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
        | FStar_Util.Inr (eff_name,uu____5634) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5647 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5654 =
        let uu____5655 = FStar_Syntax_Subst.compress t in
        uu____5655.FStar_Syntax_Syntax.n in
      match uu____5654 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5658,c) ->
          is_reifiable_comp env c
      | uu____5670 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5688)::uu____5689 -> x :: rest
        | (Binding_sig_inst uu____5694)::uu____5695 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5704 = push1 x rest1 in local :: uu____5704 in
      let uu___123_5706 = env in
      let uu____5707 = push1 s env.gamma in
      {
        solver = (uu___123_5706.solver);
        range = (uu___123_5706.range);
        curmodule = (uu___123_5706.curmodule);
        gamma = uu____5707;
        gamma_cache = (uu___123_5706.gamma_cache);
        modules = (uu___123_5706.modules);
        expected_typ = (uu___123_5706.expected_typ);
        sigtab = (uu___123_5706.sigtab);
        is_pattern = (uu___123_5706.is_pattern);
        instantiate_imp = (uu___123_5706.instantiate_imp);
        effects = (uu___123_5706.effects);
        generalize = (uu___123_5706.generalize);
        letrecs = (uu___123_5706.letrecs);
        top_level = (uu___123_5706.top_level);
        check_uvars = (uu___123_5706.check_uvars);
        use_eq = (uu___123_5706.use_eq);
        is_iface = (uu___123_5706.is_iface);
        admit = (uu___123_5706.admit);
        lax = (uu___123_5706.lax);
        lax_universes = (uu___123_5706.lax_universes);
        type_of = (uu___123_5706.type_of);
        universe_of = (uu___123_5706.universe_of);
        use_bv_sorts = (uu___123_5706.use_bv_sorts);
        qname_and_index = (uu___123_5706.qname_and_index);
        proof_ns = (uu___123_5706.proof_ns);
        synth = (uu___123_5706.synth)
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
      let uu___124_5734 = env in
      {
        solver = (uu___124_5734.solver);
        range = (uu___124_5734.range);
        curmodule = (uu___124_5734.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5734.gamma_cache);
        modules = (uu___124_5734.modules);
        expected_typ = (uu___124_5734.expected_typ);
        sigtab = (uu___124_5734.sigtab);
        is_pattern = (uu___124_5734.is_pattern);
        instantiate_imp = (uu___124_5734.instantiate_imp);
        effects = (uu___124_5734.effects);
        generalize = (uu___124_5734.generalize);
        letrecs = (uu___124_5734.letrecs);
        top_level = (uu___124_5734.top_level);
        check_uvars = (uu___124_5734.check_uvars);
        use_eq = (uu___124_5734.use_eq);
        is_iface = (uu___124_5734.is_iface);
        admit = (uu___124_5734.admit);
        lax = (uu___124_5734.lax);
        lax_universes = (uu___124_5734.lax_universes);
        type_of = (uu___124_5734.type_of);
        universe_of = (uu___124_5734.universe_of);
        use_bv_sorts = (uu___124_5734.use_bv_sorts);
        qname_and_index = (uu___124_5734.qname_and_index);
        proof_ns = (uu___124_5734.proof_ns);
        synth = (uu___124_5734.synth)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5755 = env in
             {
               solver = (uu___125_5755.solver);
               range = (uu___125_5755.range);
               curmodule = (uu___125_5755.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5755.gamma_cache);
               modules = (uu___125_5755.modules);
               expected_typ = (uu___125_5755.expected_typ);
               sigtab = (uu___125_5755.sigtab);
               is_pattern = (uu___125_5755.is_pattern);
               instantiate_imp = (uu___125_5755.instantiate_imp);
               effects = (uu___125_5755.effects);
               generalize = (uu___125_5755.generalize);
               letrecs = (uu___125_5755.letrecs);
               top_level = (uu___125_5755.top_level);
               check_uvars = (uu___125_5755.check_uvars);
               use_eq = (uu___125_5755.use_eq);
               is_iface = (uu___125_5755.is_iface);
               admit = (uu___125_5755.admit);
               lax = (uu___125_5755.lax);
               lax_universes = (uu___125_5755.lax_universes);
               type_of = (uu___125_5755.type_of);
               universe_of = (uu___125_5755.universe_of);
               use_bv_sorts = (uu___125_5755.use_bv_sorts);
               qname_and_index = (uu___125_5755.qname_and_index);
               proof_ns = (uu___125_5755.proof_ns);
               synth = (uu___125_5755.synth)
             }))
    | uu____5756 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5769  ->
             match uu____5769 with | (x,uu____5773) -> push_bv env1 x) env bs
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
            let uu___126_5793 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5793.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5793.FStar_Syntax_Syntax.index);
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
      (let uu___127_5823 = env in
       {
         solver = (uu___127_5823.solver);
         range = (uu___127_5823.range);
         curmodule = (uu___127_5823.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5823.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5823.sigtab);
         is_pattern = (uu___127_5823.is_pattern);
         instantiate_imp = (uu___127_5823.instantiate_imp);
         effects = (uu___127_5823.effects);
         generalize = (uu___127_5823.generalize);
         letrecs = (uu___127_5823.letrecs);
         top_level = (uu___127_5823.top_level);
         check_uvars = (uu___127_5823.check_uvars);
         use_eq = (uu___127_5823.use_eq);
         is_iface = (uu___127_5823.is_iface);
         admit = (uu___127_5823.admit);
         lax = (uu___127_5823.lax);
         lax_universes = (uu___127_5823.lax_universes);
         type_of = (uu___127_5823.type_of);
         universe_of = (uu___127_5823.universe_of);
         use_bv_sorts = (uu___127_5823.use_bv_sorts);
         qname_and_index = (uu___127_5823.qname_and_index);
         proof_ns = (uu___127_5823.proof_ns);
         synth = (uu___127_5823.synth)
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
        let uu____5847 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5847 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5863 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5863)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5873 = env in
      {
        solver = (uu___128_5873.solver);
        range = (uu___128_5873.range);
        curmodule = (uu___128_5873.curmodule);
        gamma = (uu___128_5873.gamma);
        gamma_cache = (uu___128_5873.gamma_cache);
        modules = (uu___128_5873.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5873.sigtab);
        is_pattern = (uu___128_5873.is_pattern);
        instantiate_imp = (uu___128_5873.instantiate_imp);
        effects = (uu___128_5873.effects);
        generalize = (uu___128_5873.generalize);
        letrecs = (uu___128_5873.letrecs);
        top_level = (uu___128_5873.top_level);
        check_uvars = (uu___128_5873.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5873.is_iface);
        admit = (uu___128_5873.admit);
        lax = (uu___128_5873.lax);
        lax_universes = (uu___128_5873.lax_universes);
        type_of = (uu___128_5873.type_of);
        universe_of = (uu___128_5873.universe_of);
        use_bv_sorts = (uu___128_5873.use_bv_sorts);
        qname_and_index = (uu___128_5873.qname_and_index);
        proof_ns = (uu___128_5873.proof_ns);
        synth = (uu___128_5873.synth)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5889 = expected_typ env_ in
    ((let uu___129_5892 = env_ in
      {
        solver = (uu___129_5892.solver);
        range = (uu___129_5892.range);
        curmodule = (uu___129_5892.curmodule);
        gamma = (uu___129_5892.gamma);
        gamma_cache = (uu___129_5892.gamma_cache);
        modules = (uu___129_5892.modules);
        expected_typ = None;
        sigtab = (uu___129_5892.sigtab);
        is_pattern = (uu___129_5892.is_pattern);
        instantiate_imp = (uu___129_5892.instantiate_imp);
        effects = (uu___129_5892.effects);
        generalize = (uu___129_5892.generalize);
        letrecs = (uu___129_5892.letrecs);
        top_level = (uu___129_5892.top_level);
        check_uvars = (uu___129_5892.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5892.is_iface);
        admit = (uu___129_5892.admit);
        lax = (uu___129_5892.lax);
        lax_universes = (uu___129_5892.lax_universes);
        type_of = (uu___129_5892.type_of);
        universe_of = (uu___129_5892.universe_of);
        use_bv_sorts = (uu___129_5892.use_bv_sorts);
        qname_and_index = (uu___129_5892.qname_and_index);
        proof_ns = (uu___129_5892.proof_ns);
        synth = (uu___129_5892.synth)
      }), uu____5889)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5903 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5907  ->
                    match uu___108_5907 with
                    | Binding_sig (uu____5909,se) -> [se]
                    | uu____5913 -> [])) in
          FStar_All.pipe_right uu____5903 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5918 = env in
       {
         solver = (uu___130_5918.solver);
         range = (uu___130_5918.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5918.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5918.expected_typ);
         sigtab = (uu___130_5918.sigtab);
         is_pattern = (uu___130_5918.is_pattern);
         instantiate_imp = (uu___130_5918.instantiate_imp);
         effects = (uu___130_5918.effects);
         generalize = (uu___130_5918.generalize);
         letrecs = (uu___130_5918.letrecs);
         top_level = (uu___130_5918.top_level);
         check_uvars = (uu___130_5918.check_uvars);
         use_eq = (uu___130_5918.use_eq);
         is_iface = (uu___130_5918.is_iface);
         admit = (uu___130_5918.admit);
         lax = (uu___130_5918.lax);
         lax_universes = (uu___130_5918.lax_universes);
         type_of = (uu___130_5918.type_of);
         universe_of = (uu___130_5918.universe_of);
         use_bv_sorts = (uu___130_5918.use_bv_sorts);
         qname_and_index = (uu___130_5918.qname_and_index);
         proof_ns = (uu___130_5918.proof_ns);
         synth = (uu___130_5918.synth)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5968)::tl1 -> aux out tl1
      | (Binding_lid (uu____5971,(uu____5972,t)))::tl1 ->
          let uu____5981 =
            let uu____5985 = FStar_Syntax_Free.uvars t in ext out uu____5985 in
          aux uu____5981 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5989;
            FStar_Syntax_Syntax.index = uu____5990;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5996 =
            let uu____6000 = FStar_Syntax_Free.uvars t in ext out uu____6000 in
          aux uu____5996 tl1
      | (Binding_sig uu____6004)::uu____6005 -> out
      | (Binding_sig_inst uu____6010)::uu____6011 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6048)::tl1 -> aux out tl1
      | (Binding_univ uu____6055)::tl1 -> aux out tl1
      | (Binding_lid (uu____6058,(uu____6059,t)))::tl1 ->
          let uu____6068 =
            let uu____6070 = FStar_Syntax_Free.univs t in ext out uu____6070 in
          aux uu____6068 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6072;
            FStar_Syntax_Syntax.index = uu____6073;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6079 =
            let uu____6081 = FStar_Syntax_Free.univs t in ext out uu____6081 in
          aux uu____6079 tl1
      | (Binding_sig uu____6083)::uu____6084 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6121)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6131 = FStar_Util.set_add uname out in aux uu____6131 tl1
      | (Binding_lid (uu____6133,(uu____6134,t)))::tl1 ->
          let uu____6143 =
            let uu____6145 = FStar_Syntax_Free.univnames t in
            ext out uu____6145 in
          aux uu____6143 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6147;
            FStar_Syntax_Syntax.index = uu____6148;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6154 =
            let uu____6156 = FStar_Syntax_Free.univnames t in
            ext out uu____6156 in
          aux uu____6154 tl1
      | (Binding_sig uu____6158)::uu____6159 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6175  ->
            match uu___109_6175 with
            | Binding_var x -> [x]
            | Binding_lid uu____6178 -> []
            | Binding_sig uu____6181 -> []
            | Binding_univ uu____6185 -> []
            | Binding_sig_inst uu____6186 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6196 =
      let uu____6198 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6198
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6196 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6214 =
      let uu____6215 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6219  ->
                match uu___110_6219 with
                | Binding_var x ->
                    let uu____6221 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6221
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6224) ->
                    let uu____6225 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6225
                | Binding_sig (ls,uu____6227) ->
                    let uu____6230 =
                      let uu____6231 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6231
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6230
                | Binding_sig_inst (ls,uu____6237,uu____6238) ->
                    let uu____6241 =
                      let uu____6242 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6242
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6241)) in
      FStar_All.pipe_right uu____6215 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6214 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6254 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6254
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6275  ->
                 fun uu____6276  ->
                   match (uu____6275, uu____6276) with
                   | ((b1,uu____6286),(b2,uu____6288)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6331  ->
             match uu___111_6331 with
             | Binding_sig (lids,uu____6335) -> FStar_List.append lids keys
             | uu____6338 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6340  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6365) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6377,uu____6378) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6402 = list_prefix p path1 in
            if uu____6402 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6412 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6412
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6432 = e in
            {
              solver = (uu___131_6432.solver);
              range = (uu___131_6432.range);
              curmodule = (uu___131_6432.curmodule);
              gamma = (uu___131_6432.gamma);
              gamma_cache = (uu___131_6432.gamma_cache);
              modules = (uu___131_6432.modules);
              expected_typ = (uu___131_6432.expected_typ);
              sigtab = (uu___131_6432.sigtab);
              is_pattern = (uu___131_6432.is_pattern);
              instantiate_imp = (uu___131_6432.instantiate_imp);
              effects = (uu___131_6432.effects);
              generalize = (uu___131_6432.generalize);
              letrecs = (uu___131_6432.letrecs);
              top_level = (uu___131_6432.top_level);
              check_uvars = (uu___131_6432.check_uvars);
              use_eq = (uu___131_6432.use_eq);
              is_iface = (uu___131_6432.is_iface);
              admit = (uu___131_6432.admit);
              lax = (uu___131_6432.lax);
              lax_universes = (uu___131_6432.lax_universes);
              type_of = (uu___131_6432.type_of);
              universe_of = (uu___131_6432.universe_of);
              use_bv_sorts = (uu___131_6432.use_bv_sorts);
              qname_and_index = (uu___131_6432.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___131_6432.synth)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6451 = e in
    {
      solver = (uu___132_6451.solver);
      range = (uu___132_6451.range);
      curmodule = (uu___132_6451.curmodule);
      gamma = (uu___132_6451.gamma);
      gamma_cache = (uu___132_6451.gamma_cache);
      modules = (uu___132_6451.modules);
      expected_typ = (uu___132_6451.expected_typ);
      sigtab = (uu___132_6451.sigtab);
      is_pattern = (uu___132_6451.is_pattern);
      instantiate_imp = (uu___132_6451.instantiate_imp);
      effects = (uu___132_6451.effects);
      generalize = (uu___132_6451.generalize);
      letrecs = (uu___132_6451.letrecs);
      top_level = (uu___132_6451.top_level);
      check_uvars = (uu___132_6451.check_uvars);
      use_eq = (uu___132_6451.use_eq);
      is_iface = (uu___132_6451.is_iface);
      admit = (uu___132_6451.admit);
      lax = (uu___132_6451.lax);
      lax_universes = (uu___132_6451.lax_universes);
      type_of = (uu___132_6451.type_of);
      universe_of = (uu___132_6451.universe_of);
      use_bv_sorts = (uu___132_6451.use_bv_sorts);
      qname_and_index = (uu___132_6451.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___132_6451.synth)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6460::rest ->
        let uu___133_6463 = e in
        {
          solver = (uu___133_6463.solver);
          range = (uu___133_6463.range);
          curmodule = (uu___133_6463.curmodule);
          gamma = (uu___133_6463.gamma);
          gamma_cache = (uu___133_6463.gamma_cache);
          modules = (uu___133_6463.modules);
          expected_typ = (uu___133_6463.expected_typ);
          sigtab = (uu___133_6463.sigtab);
          is_pattern = (uu___133_6463.is_pattern);
          instantiate_imp = (uu___133_6463.instantiate_imp);
          effects = (uu___133_6463.effects);
          generalize = (uu___133_6463.generalize);
          letrecs = (uu___133_6463.letrecs);
          top_level = (uu___133_6463.top_level);
          check_uvars = (uu___133_6463.check_uvars);
          use_eq = (uu___133_6463.use_eq);
          is_iface = (uu___133_6463.is_iface);
          admit = (uu___133_6463.admit);
          lax = (uu___133_6463.lax);
          lax_universes = (uu___133_6463.lax_universes);
          type_of = (uu___133_6463.type_of);
          universe_of = (uu___133_6463.universe_of);
          use_bv_sorts = (uu___133_6463.use_bv_sorts);
          qname_and_index = (uu___133_6463.qname_and_index);
          proof_ns = rest;
          synth = (uu___133_6463.synth)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6473 = e in
      {
        solver = (uu___134_6473.solver);
        range = (uu___134_6473.range);
        curmodule = (uu___134_6473.curmodule);
        gamma = (uu___134_6473.gamma);
        gamma_cache = (uu___134_6473.gamma_cache);
        modules = (uu___134_6473.modules);
        expected_typ = (uu___134_6473.expected_typ);
        sigtab = (uu___134_6473.sigtab);
        is_pattern = (uu___134_6473.is_pattern);
        instantiate_imp = (uu___134_6473.instantiate_imp);
        effects = (uu___134_6473.effects);
        generalize = (uu___134_6473.generalize);
        letrecs = (uu___134_6473.letrecs);
        top_level = (uu___134_6473.top_level);
        check_uvars = (uu___134_6473.check_uvars);
        use_eq = (uu___134_6473.use_eq);
        is_iface = (uu___134_6473.is_iface);
        admit = (uu___134_6473.admit);
        lax = (uu___134_6473.lax);
        lax_universes = (uu___134_6473.lax_universes);
        type_of = (uu___134_6473.type_of);
        universe_of = (uu___134_6473.universe_of);
        use_bv_sorts = (uu___134_6473.use_bv_sorts);
        qname_and_index = (uu___134_6473.qname_and_index);
        proof_ns = ns;
        synth = (uu___134_6473.synth)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6491 =
        FStar_List.map
          (fun fpns  ->
             let uu____6502 =
               let uu____6503 =
                 let uu____6504 =
                   FStar_List.map
                     (fun uu____6509  ->
                        match uu____6509 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6504 in
               Prims.strcat uu____6503 "]" in
             Prims.strcat "[" uu____6502) pns in
      FStar_String.concat ";" uu____6491 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6518  -> ());
    push = (fun uu____6519  -> ());
    pop = (fun uu____6520  -> ());
    mark = (fun uu____6521  -> ());
    reset_mark = (fun uu____6522  -> ());
    commit_mark = (fun uu____6523  -> ());
    encode_modul = (fun uu____6524  -> fun uu____6525  -> ());
    encode_sig = (fun uu____6526  -> fun uu____6527  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6534  -> fun uu____6535  -> fun uu____6536  -> ());
    is_trivial = (fun uu____6540  -> fun uu____6541  -> false);
    finish = (fun uu____6542  -> ());
    refresh = (fun uu____6543  -> ())
  }