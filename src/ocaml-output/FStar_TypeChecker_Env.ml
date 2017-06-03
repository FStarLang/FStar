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
    match projectee with | Binding_var _0 -> true | uu____29 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____43 -> false
let __proj__Binding_lid__item___0:
  binding -> (FStar_Ident.lident* FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____64 -> false
let __proj__Binding_sig__item___0:
  binding -> (FStar_Ident.lident Prims.list* FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____85 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____101 -> false
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
    match projectee with | NoDelta  -> true | uu____127 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____131 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____135 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____140 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____151 -> false
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
      | (NoDelta ,uu____861) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____862,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____863,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____864 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____874 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____882 =
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
          let uu____921 = new_gamma_cache () in
          let uu____923 = new_sigtab () in
          let uu____925 =
            let uu____926 = FStar_Options.using_facts_from () in
            match uu____926 with
            | Some ns ->
                let uu____932 =
                  let uu____937 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____937 [([], false)] in
                [uu____932]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____921;
            modules = [];
            expected_typ = None;
            sigtab = uu____923;
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
            proof_ns = uu____925
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1015  ->
    let uu____1016 = FStar_ST.read query_indices in
    match uu____1016 with
    | [] -> failwith "Empty query indices!"
    | uu____1030 ->
        let uu____1035 =
          let uu____1040 =
            let uu____1044 = FStar_ST.read query_indices in
            FStar_List.hd uu____1044 in
          let uu____1058 = FStar_ST.read query_indices in uu____1040 ::
            uu____1058 in
        FStar_ST.write query_indices uu____1035
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1080  ->
    let uu____1081 = FStar_ST.read query_indices in
    match uu____1081 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1117  ->
    match uu____1117 with
    | (l,n1) ->
        let uu____1122 = FStar_ST.read query_indices in
        (match uu____1122 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1156 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1166  ->
    let uu____1167 = FStar_ST.read query_indices in FStar_List.hd uu____1167
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1183  ->
    let uu____1184 = FStar_ST.read query_indices in
    match uu____1184 with
    | hd1::uu____1196::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1223 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1237 =
       let uu____1239 = FStar_ST.read stack in env :: uu____1239 in
     FStar_ST.write stack uu____1237);
    (let uu___112_1247 = env in
     let uu____1248 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1250 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1247.solver);
       range = (uu___112_1247.range);
       curmodule = (uu___112_1247.curmodule);
       gamma = (uu___112_1247.gamma);
       gamma_cache = uu____1248;
       modules = (uu___112_1247.modules);
       expected_typ = (uu___112_1247.expected_typ);
       sigtab = uu____1250;
       is_pattern = (uu___112_1247.is_pattern);
       instantiate_imp = (uu___112_1247.instantiate_imp);
       effects = (uu___112_1247.effects);
       generalize = (uu___112_1247.generalize);
       letrecs = (uu___112_1247.letrecs);
       top_level = (uu___112_1247.top_level);
       check_uvars = (uu___112_1247.check_uvars);
       use_eq = (uu___112_1247.use_eq);
       is_iface = (uu___112_1247.is_iface);
       admit = (uu___112_1247.admit);
       lax = (uu___112_1247.lax);
       lax_universes = (uu___112_1247.lax_universes);
       type_of = (uu___112_1247.type_of);
       universe_of = (uu___112_1247.universe_of);
       use_bv_sorts = (uu___112_1247.use_bv_sorts);
       qname_and_index = (uu___112_1247.qname_and_index);
       proof_ns = (uu___112_1247.proof_ns)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1254  ->
    let uu____1255 = FStar_ST.read stack in
    match uu____1255 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1267 -> failwith "Impossible: Too many pops"
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
    (let uu____1299 = pop_stack () in ());
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
        let uu____1318 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1330  ->
                  match uu____1330 with
                  | (m,uu____1334) -> FStar_Ident.lid_equals l m)) in
        (match uu____1318 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1339 = env in
               {
                 solver = (uu___113_1339.solver);
                 range = (uu___113_1339.range);
                 curmodule = (uu___113_1339.curmodule);
                 gamma = (uu___113_1339.gamma);
                 gamma_cache = (uu___113_1339.gamma_cache);
                 modules = (uu___113_1339.modules);
                 expected_typ = (uu___113_1339.expected_typ);
                 sigtab = (uu___113_1339.sigtab);
                 is_pattern = (uu___113_1339.is_pattern);
                 instantiate_imp = (uu___113_1339.instantiate_imp);
                 effects = (uu___113_1339.effects);
                 generalize = (uu___113_1339.generalize);
                 letrecs = (uu___113_1339.letrecs);
                 top_level = (uu___113_1339.top_level);
                 check_uvars = (uu___113_1339.check_uvars);
                 use_eq = (uu___113_1339.use_eq);
                 is_iface = (uu___113_1339.is_iface);
                 admit = (uu___113_1339.admit);
                 lax = (uu___113_1339.lax);
                 lax_universes = (uu___113_1339.lax_universes);
                 type_of = (uu___113_1339.type_of);
                 universe_of = (uu___113_1339.universe_of);
                 use_bv_sorts = (uu___113_1339.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___113_1339.proof_ns)
               }))
         | Some (uu____1342,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1348 = env in
               {
                 solver = (uu___114_1348.solver);
                 range = (uu___114_1348.range);
                 curmodule = (uu___114_1348.curmodule);
                 gamma = (uu___114_1348.gamma);
                 gamma_cache = (uu___114_1348.gamma_cache);
                 modules = (uu___114_1348.modules);
                 expected_typ = (uu___114_1348.expected_typ);
                 sigtab = (uu___114_1348.sigtab);
                 is_pattern = (uu___114_1348.is_pattern);
                 instantiate_imp = (uu___114_1348.instantiate_imp);
                 effects = (uu___114_1348.effects);
                 generalize = (uu___114_1348.generalize);
                 letrecs = (uu___114_1348.letrecs);
                 top_level = (uu___114_1348.top_level);
                 check_uvars = (uu___114_1348.check_uvars);
                 use_eq = (uu___114_1348.use_eq);
                 is_iface = (uu___114_1348.is_iface);
                 admit = (uu___114_1348.admit);
                 lax = (uu___114_1348.lax);
                 lax_universes = (uu___114_1348.lax_universes);
                 type_of = (uu___114_1348.type_of);
                 universe_of = (uu___114_1348.universe_of);
                 use_bv_sorts = (uu___114_1348.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___114_1348.proof_ns)
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
        (let uu___115_1364 = e in
         {
           solver = (uu___115_1364.solver);
           range = r;
           curmodule = (uu___115_1364.curmodule);
           gamma = (uu___115_1364.gamma);
           gamma_cache = (uu___115_1364.gamma_cache);
           modules = (uu___115_1364.modules);
           expected_typ = (uu___115_1364.expected_typ);
           sigtab = (uu___115_1364.sigtab);
           is_pattern = (uu___115_1364.is_pattern);
           instantiate_imp = (uu___115_1364.instantiate_imp);
           effects = (uu___115_1364.effects);
           generalize = (uu___115_1364.generalize);
           letrecs = (uu___115_1364.letrecs);
           top_level = (uu___115_1364.top_level);
           check_uvars = (uu___115_1364.check_uvars);
           use_eq = (uu___115_1364.use_eq);
           is_iface = (uu___115_1364.is_iface);
           admit = (uu___115_1364.admit);
           lax = (uu___115_1364.lax);
           lax_universes = (uu___115_1364.lax_universes);
           type_of = (uu___115_1364.type_of);
           universe_of = (uu___115_1364.universe_of);
           use_bv_sorts = (uu___115_1364.use_bv_sorts);
           qname_and_index = (uu___115_1364.qname_and_index);
           proof_ns = (uu___115_1364.proof_ns)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1381 = env in
      {
        solver = (uu___116_1381.solver);
        range = (uu___116_1381.range);
        curmodule = lid;
        gamma = (uu___116_1381.gamma);
        gamma_cache = (uu___116_1381.gamma_cache);
        modules = (uu___116_1381.modules);
        expected_typ = (uu___116_1381.expected_typ);
        sigtab = (uu___116_1381.sigtab);
        is_pattern = (uu___116_1381.is_pattern);
        instantiate_imp = (uu___116_1381.instantiate_imp);
        effects = (uu___116_1381.effects);
        generalize = (uu___116_1381.generalize);
        letrecs = (uu___116_1381.letrecs);
        top_level = (uu___116_1381.top_level);
        check_uvars = (uu___116_1381.check_uvars);
        use_eq = (uu___116_1381.use_eq);
        is_iface = (uu___116_1381.is_iface);
        admit = (uu___116_1381.admit);
        lax = (uu___116_1381.lax);
        lax_universes = (uu___116_1381.lax_universes);
        type_of = (uu___116_1381.type_of);
        universe_of = (uu___116_1381.universe_of);
        use_bv_sorts = (uu___116_1381.use_bv_sorts);
        qname_and_index = (uu___116_1381.qname_and_index);
        proof_ns = (uu___116_1381.proof_ns)
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
    let uu____1403 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1403
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1406  ->
    let uu____1407 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1407
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1429) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1448 = FStar_Syntax_Subst.subst vs t in (us, uu____1448)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1453  ->
    match uu___100_1453 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1467  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1477 = inst_tscheme t in
      match uu____1477 with
      | (us,t1) ->
          let uu____1484 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1484)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1496  ->
          match uu____1496 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1514 =
                         let uu____1515 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1520 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1525 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1526 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1515 uu____1520 uu____1525 uu____1526 in
                       failwith uu____1514)
                    else ();
                    (let uu____1528 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1528))
               | uu____1532 ->
                   let uu____1533 =
                     let uu____1534 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1534 in
                   failwith uu____1533)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1538 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1542 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1546 -> false
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
             | ([],uu____1572) -> Maybe
             | (uu____1576,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1588 -> No in
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
          let uu____1648 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1648 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1669  ->
                   match uu___101_1669 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1692 =
                           let uu____1702 =
                             let uu____1710 = inst_tscheme t in
                             FStar_Util.Inl uu____1710 in
                           (uu____1702, (FStar_Ident.range_of_lid l)) in
                         Some uu____1692
                       else None
                   | Binding_sig
                       (uu____1744,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1746);
                                     FStar_Syntax_Syntax.sigrng = uu____1747;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1748;
                                     FStar_Syntax_Syntax.sigmeta = uu____1749;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1758 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1758
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1785 ->
                             Some t
                         | uu____1789 -> cache t in
                       let uu____1790 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1790 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1830 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1830 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1874 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1916 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1916
         then
           let uu____1927 = find_in_sigtab env lid in
           match uu____1927 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1993) ->
          add_sigelts env ses
      | uu____1998 ->
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
            | uu____2007 -> ()))
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
        (fun uu___102_2025  ->
           match uu___102_2025 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2038 -> None)
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
          ((uu____2059,lb::[]),uu____2061,uu____2062) ->
          let uu____2071 =
            let uu____2076 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2082 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2076, uu____2082) in
          Some uu____2071
      | FStar_Syntax_Syntax.Sig_let ((uu____2089,lbs),uu____2091,uu____2092)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2112 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2119 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2119
                   then
                     let uu____2125 =
                       let uu____2130 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2136 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2130, uu____2136) in
                     Some uu____2125
                   else None)
      | uu____2148 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2167 =
          let uu____2172 =
            let uu____2175 =
              let uu____2176 =
                let uu____2179 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2179 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2176) in
            inst_tscheme uu____2175 in
          (uu____2172, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2167
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2193,uu____2194) ->
        let uu____2197 =
          let uu____2202 =
            let uu____2205 =
              let uu____2206 =
                let uu____2209 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2209 in
              (us, uu____2206) in
            inst_tscheme uu____2205 in
          (uu____2202, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2197
    | uu____2220 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2255 =
        match uu____2255 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2305,uvs,t,uu____2308,uu____2309,uu____2310);
                    FStar_Syntax_Syntax.sigrng = uu____2311;
                    FStar_Syntax_Syntax.sigquals = uu____2312;
                    FStar_Syntax_Syntax.sigmeta = uu____2313;_},None
                  )
                 ->
                 let uu____2323 =
                   let uu____2328 = inst_tscheme (uvs, t) in
                   (uu____2328, rng) in
                 Some uu____2323
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2340;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2342;_},None
                  )
                 ->
                 let uu____2350 =
                   let uu____2351 = in_cur_mod env l in uu____2351 = Yes in
                 if uu____2350
                 then
                   let uu____2357 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2357
                    then
                      let uu____2364 =
                        let uu____2369 = inst_tscheme (uvs, t) in
                        (uu____2369, rng) in
                      Some uu____2364
                    else None)
                 else
                   (let uu____2384 =
                      let uu____2389 = inst_tscheme (uvs, t) in
                      (uu____2389, rng) in
                    Some uu____2384)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2402,uu____2403);
                    FStar_Syntax_Syntax.sigrng = uu____2404;
                    FStar_Syntax_Syntax.sigquals = uu____2405;
                    FStar_Syntax_Syntax.sigmeta = uu____2406;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2425 =
                        let uu____2430 = inst_tscheme (uvs, k) in
                        (uu____2430, rng) in
                      Some uu____2425
                  | uu____2439 ->
                      let uu____2440 =
                        let uu____2445 =
                          let uu____2448 =
                            let uu____2449 =
                              let uu____2452 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2452 in
                            (uvs, uu____2449) in
                          inst_tscheme uu____2448 in
                        (uu____2445, rng) in
                      Some uu____2440)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2467,uu____2468);
                    FStar_Syntax_Syntax.sigrng = uu____2469;
                    FStar_Syntax_Syntax.sigquals = uu____2470;
                    FStar_Syntax_Syntax.sigmeta = uu____2471;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2491 =
                        let uu____2496 = inst_tscheme_with (uvs, k) us in
                        (uu____2496, rng) in
                      Some uu____2491
                  | uu____2505 ->
                      let uu____2506 =
                        let uu____2511 =
                          let uu____2514 =
                            let uu____2515 =
                              let uu____2518 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2518 in
                            (uvs, uu____2515) in
                          inst_tscheme_with uu____2514 us in
                        (uu____2511, rng) in
                      Some uu____2506)
             | FStar_Util.Inr se ->
                 let uu____2538 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2549;
                        FStar_Syntax_Syntax.sigrng = uu____2550;
                        FStar_Syntax_Syntax.sigquals = uu____2551;
                        FStar_Syntax_Syntax.sigmeta = uu____2552;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2561 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2538
                   (FStar_Util.map_option
                      (fun uu____2584  ->
                         match uu____2584 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2601 =
        let uu____2607 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2607 mapper in
      match uu____2601 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2659 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2659.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2659.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2659.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2680 = lookup_qname env l in
      match uu____2680 with | None  -> false | Some uu____2700 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2728 = try_lookup_bv env bv in
      match uu____2728 with
      | None  ->
          let uu____2736 =
            let uu____2737 =
              let uu____2740 = variable_not_found bv in (uu____2740, bvr) in
            FStar_Errors.Error uu____2737 in
          raise uu____2736
      | Some (t,r) ->
          let uu____2747 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2748 = FStar_Range.set_use_range r bvr in
          (uu____2747, uu____2748)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2760 = try_lookup_lid_aux env l in
      match uu____2760 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2802 =
            let uu____2807 =
              let uu____2810 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2810) in
            (uu____2807, r1) in
          Some uu____2802
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2827 = try_lookup_lid env l in
      match uu____2827 with
      | None  ->
          let uu____2841 =
            let uu____2842 =
              let uu____2845 = name_not_found l in
              (uu____2845, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2842 in
          raise uu____2841
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2866  ->
              match uu___103_2866 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2868 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2879 = lookup_qname env lid in
      match uu____2879 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2894,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2897;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2899;_},None
            ),uu____2900)
          ->
          let uu____2924 =
            let uu____2930 =
              let uu____2933 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2933) in
            (uu____2930, q) in
          Some uu____2924
      | uu____2942 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2964 = lookup_qname env lid in
      match uu____2964 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2977,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2980;
              FStar_Syntax_Syntax.sigquals = uu____2981;
              FStar_Syntax_Syntax.sigmeta = uu____2982;_},None
            ),uu____2983)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3007 ->
          let uu____3018 =
            let uu____3019 =
              let uu____3022 = name_not_found lid in
              (uu____3022, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3019 in
          raise uu____3018
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3033 = lookup_qname env lid in
      match uu____3033 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3046,uvs,t,uu____3049,uu____3050,uu____3051);
              FStar_Syntax_Syntax.sigrng = uu____3052;
              FStar_Syntax_Syntax.sigquals = uu____3053;
              FStar_Syntax_Syntax.sigmeta = uu____3054;_},None
            ),uu____3055)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3081 ->
          let uu____3092 =
            let uu____3093 =
              let uu____3096 = name_not_found lid in
              (uu____3096, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3093 in
          raise uu____3092
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3108 = lookup_qname env lid in
      match uu____3108 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3122,uu____3123,uu____3124,uu____3125,uu____3126,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3128;
              FStar_Syntax_Syntax.sigquals = uu____3129;
              FStar_Syntax_Syntax.sigmeta = uu____3130;_},uu____3131),uu____3132)
          -> (true, dcs)
      | uu____3162 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3180 = lookup_qname env lid in
      match uu____3180 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3191,uu____3192,uu____3193,l,uu____3195,uu____3196);
              FStar_Syntax_Syntax.sigrng = uu____3197;
              FStar_Syntax_Syntax.sigquals = uu____3198;
              FStar_Syntax_Syntax.sigmeta = uu____3199;_},uu____3200),uu____3201)
          -> l
      | uu____3228 ->
          let uu____3239 =
            let uu____3240 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3240 in
          failwith uu____3239
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
        let uu____3264 = lookup_qname env lid in
        match uu____3264 with
        | Some (FStar_Util.Inr (se,None ),uu____3279) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3305,lbs),uu____3307,uu____3308) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3325 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3325
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3346 -> None)
        | uu____3349 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3370 = lookup_qname env ftv in
      match uu____3370 with
      | Some (FStar_Util.Inr (se,None ),uu____3383) ->
          let uu____3406 = effect_signature se in
          (match uu____3406 with
           | None  -> None
           | Some ((uu____3417,t),r) ->
               let uu____3426 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3426)
      | uu____3427 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3444 = try_lookup_effect_lid env ftv in
      match uu____3444 with
      | None  ->
          let uu____3446 =
            let uu____3447 =
              let uu____3450 = name_not_found ftv in
              (uu____3450, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3447 in
          raise uu____3446
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
        let uu____3464 = lookup_qname env lid0 in
        match uu____3464 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3482);
                FStar_Syntax_Syntax.sigrng = uu____3483;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3485;_},None
              ),uu____3486)
            ->
            let lid1 =
              let uu____3513 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3513 in
            let uu____3514 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3516  ->
                      match uu___104_3516 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3517 -> false)) in
            if uu____3514
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
                     (let uu____3539 =
                        let uu____3540 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3541 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3540 uu____3541 in
                      failwith uu____3539) in
               match (binders, univs1) with
               | ([],uu____3549) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3558,uu____3559::uu____3560::uu____3561) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3564 =
                     let uu____3565 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3566 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3565 uu____3566 in
                   failwith uu____3564
               | uu____3574 ->
                   let uu____3577 =
                     let uu____3580 =
                       let uu____3581 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3581) in
                     inst_tscheme_with uu____3580 insts in
                   (match uu____3577 with
                    | (uu____3589,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3592 =
                          let uu____3593 = FStar_Syntax_Subst.compress t1 in
                          uu____3593.FStar_Syntax_Syntax.n in
                        (match uu____3592 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3623 -> failwith "Impossible")))
        | uu____3627 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3653 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3653 with
        | None  -> None
        | Some (uu____3660,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3665 = find1 l2 in
            (match uu____3665 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3670 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3670 with
        | Some l1 -> l1
        | None  ->
            let uu____3673 = find1 l in
            (match uu____3673 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3685 = lookup_qname env l1 in
      match uu____3685 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3697;
              FStar_Syntax_Syntax.sigrng = uu____3698;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3700;_},uu____3701),uu____3702)
          -> q
      | uu____3727 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3750 =
          let uu____3751 =
            let uu____3752 = FStar_Util.string_of_int i in
            let uu____3753 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3752 uu____3753 in
          failwith uu____3751 in
        let uu____3754 = lookup_datacon env lid in
        match uu____3754 with
        | (uu____3757,t) ->
            let uu____3759 =
              let uu____3760 = FStar_Syntax_Subst.compress t in
              uu____3760.FStar_Syntax_Syntax.n in
            (match uu____3759 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3764) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3787 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3787 FStar_Pervasives.fst)
             | uu____3792 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3799 = lookup_qname env l in
      match uu____3799 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3810,uu____3811,uu____3812);
              FStar_Syntax_Syntax.sigrng = uu____3813;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3815;_},uu____3816),uu____3817)
          ->
          FStar_Util.for_some
            (fun uu___105_3842  ->
               match uu___105_3842 with
               | FStar_Syntax_Syntax.Projector uu____3843 -> true
               | uu____3846 -> false) quals
      | uu____3847 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3864 = lookup_qname env lid in
      match uu____3864 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3875,uu____3876,uu____3877,uu____3878,uu____3879,uu____3880);
              FStar_Syntax_Syntax.sigrng = uu____3881;
              FStar_Syntax_Syntax.sigquals = uu____3882;
              FStar_Syntax_Syntax.sigmeta = uu____3883;_},uu____3884),uu____3885)
          -> true
      | uu____3912 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3929 = lookup_qname env lid in
      match uu____3929 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3940,uu____3941,uu____3942,uu____3943,uu____3944,uu____3945);
              FStar_Syntax_Syntax.sigrng = uu____3946;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3948;_},uu____3949),uu____3950)
          ->
          FStar_Util.for_some
            (fun uu___106_3979  ->
               match uu___106_3979 with
               | FStar_Syntax_Syntax.RecordType uu____3980 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3985 -> true
               | uu____3990 -> false) quals
      | uu____3991 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4008 = lookup_qname env lid in
      match uu____4008 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4019,uu____4020,uu____4021);
              FStar_Syntax_Syntax.sigrng = uu____4022;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4024;_},uu____4025),uu____4026)
          ->
          FStar_Util.for_some
            (fun uu___107_4055  ->
               match uu___107_4055 with
               | FStar_Syntax_Syntax.Action uu____4056 -> true
               | uu____4057 -> false) quals
      | uu____4058 -> false
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
      let uu____4077 =
        let uu____4078 = FStar_Syntax_Util.un_uinst head1 in
        uu____4078.FStar_Syntax_Syntax.n in
      match uu____4077 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4082 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4120 -> Some false
        | FStar_Util.Inr (se,uu____4129) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4138 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4142 -> Some true
             | uu____4151 -> Some false) in
      let uu____4152 =
        let uu____4154 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4154 mapper in
      match uu____4152 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4181 = lookup_qname env lid in
      match uu____4181 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4192,uu____4193,tps,uu____4195,uu____4196,uu____4197);
              FStar_Syntax_Syntax.sigrng = uu____4198;
              FStar_Syntax_Syntax.sigquals = uu____4199;
              FStar_Syntax_Syntax.sigmeta = uu____4200;_},uu____4201),uu____4202)
          -> FStar_List.length tps
      | uu____4235 ->
          let uu____4246 =
            let uu____4247 =
              let uu____4250 = name_not_found lid in
              (uu____4250, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4247 in
          raise uu____4246
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
           (fun uu____4272  ->
              match uu____4272 with
              | (d,uu____4277) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4286 = effect_decl_opt env l in
      match uu____4286 with
      | None  ->
          let uu____4294 =
            let uu____4295 =
              let uu____4298 = name_not_found l in
              (uu____4298, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4295 in
          raise uu____4294
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
            (let uu____4341 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4365  ->
                       match uu____4365 with
                       | (m1,m2,uu____4373,uu____4374,uu____4375) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4341 with
             | None  ->
                 let uu____4384 =
                   let uu____4385 =
                     let uu____4388 =
                       let uu____4389 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4390 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4389
                         uu____4390 in
                     (uu____4388, (env.range)) in
                   FStar_Errors.Error uu____4385 in
                 raise uu____4384
             | Some (uu____4394,uu____4395,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4442 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4454  ->
            match uu____4454 with
            | (d,uu____4458) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4442 with
  | None  ->
      let uu____4465 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4465
  | Some (md,_q) ->
      let uu____4474 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4474 with
       | (uu____4481,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4489)::(wp,uu____4491)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4513 -> failwith "Impossible"))
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
                 let uu____4549 = get_range env in
                 let uu____4550 =
                   let uu____4553 =
                     let uu____4554 =
                       let uu____4564 =
                         let uu____4566 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4566] in
                       (null_wp, uu____4564) in
                     FStar_Syntax_Syntax.Tm_app uu____4554 in
                   FStar_Syntax_Syntax.mk uu____4553 in
                 uu____4550 None uu____4549 in
               let uu____4576 =
                 let uu____4577 =
                   let uu____4583 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4583] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4577;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4576)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4592 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4592.order);
              joins = (uu___118_4592.joins)
            } in
          let uu___119_4597 = env in
          {
            solver = (uu___119_4597.solver);
            range = (uu___119_4597.range);
            curmodule = (uu___119_4597.curmodule);
            gamma = (uu___119_4597.gamma);
            gamma_cache = (uu___119_4597.gamma_cache);
            modules = (uu___119_4597.modules);
            expected_typ = (uu___119_4597.expected_typ);
            sigtab = (uu___119_4597.sigtab);
            is_pattern = (uu___119_4597.is_pattern);
            instantiate_imp = (uu___119_4597.instantiate_imp);
            effects;
            generalize = (uu___119_4597.generalize);
            letrecs = (uu___119_4597.letrecs);
            top_level = (uu___119_4597.top_level);
            check_uvars = (uu___119_4597.check_uvars);
            use_eq = (uu___119_4597.use_eq);
            is_iface = (uu___119_4597.is_iface);
            admit = (uu___119_4597.admit);
            lax = (uu___119_4597.lax);
            lax_universes = (uu___119_4597.lax_universes);
            type_of = (uu___119_4597.type_of);
            universe_of = (uu___119_4597.universe_of);
            use_bv_sorts = (uu___119_4597.use_bv_sorts);
            qname_and_index = (uu___119_4597.qname_and_index);
            proof_ns = (uu___119_4597.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4614 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4614 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4693 = (e1.mlift).mlift_wp t wp in
                              let uu____4694 = l1 t wp e in
                              l2 t uu____4693 uu____4694))
                | uu____4695 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4730 = inst_tscheme lift_t in
            match uu____4730 with
            | (uu____4735,lift_t1) ->
                let uu____4737 =
                  let uu____4740 =
                    let uu____4741 =
                      let uu____4751 =
                        let uu____4753 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4754 =
                          let uu____4756 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4756] in
                        uu____4753 :: uu____4754 in
                      (lift_t1, uu____4751) in
                    FStar_Syntax_Syntax.Tm_app uu____4741 in
                  FStar_Syntax_Syntax.mk uu____4740 in
                uu____4737 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4801 = inst_tscheme lift_t in
            match uu____4801 with
            | (uu____4806,lift_t1) ->
                let uu____4808 =
                  let uu____4811 =
                    let uu____4812 =
                      let uu____4822 =
                        let uu____4824 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4825 =
                          let uu____4827 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4828 =
                            let uu____4830 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4830] in
                          uu____4827 :: uu____4828 in
                        uu____4824 :: uu____4825 in
                      (lift_t1, uu____4822) in
                    FStar_Syntax_Syntax.Tm_app uu____4812 in
                  FStar_Syntax_Syntax.mk uu____4811 in
                uu____4808 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4871 =
                let uu____4872 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4872
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4871 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4876 =
              let uu____4877 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4877 in
            let uu____4878 =
              let uu____4879 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4894 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4894) in
              FStar_Util.dflt "none" uu____4879 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4876
              uu____4878 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4907  ->
                    match uu____4907 with
                    | (e,uu____4912) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4925 =
            match uu____4925 with
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
              let uu____4950 =
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
                                    (let uu____4962 =
                                       let uu____4967 =
                                         find_edge order1 (i, k) in
                                       let uu____4969 =
                                         find_edge order1 (k, j) in
                                       (uu____4967, uu____4969) in
                                     match uu____4962 with
                                     | (Some e1,Some e2) ->
                                         let uu____4978 = compose_edges e1 e2 in
                                         [uu____4978]
                                     | uu____4979 -> []))))) in
              FStar_List.append order1 uu____4950 in
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
                   let uu____4994 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4995 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4995
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4994
                   then
                     let uu____4998 =
                       let uu____4999 =
                         let uu____5002 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____5003 = get_range env in
                         (uu____5002, uu____5003) in
                       FStar_Errors.Error uu____4999 in
                     raise uu____4998
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
                                            let uu____5066 =
                                              let uu____5071 =
                                                find_edge order2 (i, k) in
                                              let uu____5073 =
                                                find_edge order2 (j, k) in
                                              (uu____5071, uu____5073) in
                                            match uu____5066 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5096,uu____5097)
                                                     ->
                                                     let uu____5101 =
                                                       let uu____5104 =
                                                         let uu____5105 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5105 in
                                                       let uu____5107 =
                                                         let uu____5108 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5108 in
                                                       (uu____5104,
                                                         uu____5107) in
                                                     (match uu____5101 with
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
                                            | uu____5127 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5166 = env.effects in
              { decls = (uu___120_5166.decls); order = order2; joins } in
            let uu___121_5167 = env in
            {
              solver = (uu___121_5167.solver);
              range = (uu___121_5167.range);
              curmodule = (uu___121_5167.curmodule);
              gamma = (uu___121_5167.gamma);
              gamma_cache = (uu___121_5167.gamma_cache);
              modules = (uu___121_5167.modules);
              expected_typ = (uu___121_5167.expected_typ);
              sigtab = (uu___121_5167.sigtab);
              is_pattern = (uu___121_5167.is_pattern);
              instantiate_imp = (uu___121_5167.instantiate_imp);
              effects;
              generalize = (uu___121_5167.generalize);
              letrecs = (uu___121_5167.letrecs);
              top_level = (uu___121_5167.top_level);
              check_uvars = (uu___121_5167.check_uvars);
              use_eq = (uu___121_5167.use_eq);
              is_iface = (uu___121_5167.is_iface);
              admit = (uu___121_5167.admit);
              lax = (uu___121_5167.lax);
              lax_universes = (uu___121_5167.lax_universes);
              type_of = (uu___121_5167.type_of);
              universe_of = (uu___121_5167.universe_of);
              use_bv_sorts = (uu___121_5167.use_bv_sorts);
              qname_and_index = (uu___121_5167.qname_and_index);
              proof_ns = (uu___121_5167.proof_ns)
            }))
      | uu____5168 -> env
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
        | uu____5190 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5198 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5198 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5208 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5208 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5230 =
                     let uu____5231 =
                       let uu____5234 =
                         let uu____5235 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5244 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5255 =
                           let uu____5256 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5256 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5235 uu____5244 uu____5255 in
                       (uu____5234, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5231 in
                   raise uu____5230)
                else ();
                (let inst1 =
                   let uu____5260 =
                     let uu____5266 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5266 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5273  ->
                        fun uu____5274  ->
                          match (uu____5273, uu____5274) with
                          | ((x,uu____5288),(t,uu____5290)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5260 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5305 =
                     let uu___122_5306 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5306.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5306.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5306.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5306.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5305
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5336 =
    let uu____5341 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5341 in
  match uu____5336 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5357 =
        only_reifiable &&
          (let uu____5358 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5358) in
      if uu____5357
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5371 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5373 =
               let uu____5382 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5382) in
             (match uu____5373 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5416 =
                    let uu____5419 = get_range env in
                    let uu____5420 =
                      let uu____5423 =
                        let uu____5424 =
                          let uu____5434 =
                            let uu____5436 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5436; wp] in
                          (repr, uu____5434) in
                        FStar_Syntax_Syntax.Tm_app uu____5424 in
                      FStar_Syntax_Syntax.mk uu____5423 in
                    uu____5420 None uu____5419 in
                  Some uu____5416))
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
          let uu____5480 =
            let uu____5481 =
              let uu____5484 =
                let uu____5485 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5485 in
              let uu____5486 = get_range env in (uu____5484, uu____5486) in
            FStar_Errors.Error uu____5481 in
          raise uu____5480 in
        let uu____5487 = effect_repr_aux true env c u_c in
        match uu____5487 with
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
        | FStar_Util.Inr (eff_name,uu____5519) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5532 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5539 =
        let uu____5540 = FStar_Syntax_Subst.compress t in
        uu____5540.FStar_Syntax_Syntax.n in
      match uu____5539 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5543,c) ->
          is_reifiable_comp env c
      | uu____5555 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5573)::uu____5574 -> x :: rest
        | (Binding_sig_inst uu____5579)::uu____5580 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5589 = push1 x rest1 in local :: uu____5589 in
      let uu___123_5591 = env in
      let uu____5592 = push1 s env.gamma in
      {
        solver = (uu___123_5591.solver);
        range = (uu___123_5591.range);
        curmodule = (uu___123_5591.curmodule);
        gamma = uu____5592;
        gamma_cache = (uu___123_5591.gamma_cache);
        modules = (uu___123_5591.modules);
        expected_typ = (uu___123_5591.expected_typ);
        sigtab = (uu___123_5591.sigtab);
        is_pattern = (uu___123_5591.is_pattern);
        instantiate_imp = (uu___123_5591.instantiate_imp);
        effects = (uu___123_5591.effects);
        generalize = (uu___123_5591.generalize);
        letrecs = (uu___123_5591.letrecs);
        top_level = (uu___123_5591.top_level);
        check_uvars = (uu___123_5591.check_uvars);
        use_eq = (uu___123_5591.use_eq);
        is_iface = (uu___123_5591.is_iface);
        admit = (uu___123_5591.admit);
        lax = (uu___123_5591.lax);
        lax_universes = (uu___123_5591.lax_universes);
        type_of = (uu___123_5591.type_of);
        universe_of = (uu___123_5591.universe_of);
        use_bv_sorts = (uu___123_5591.use_bv_sorts);
        qname_and_index = (uu___123_5591.qname_and_index);
        proof_ns = (uu___123_5591.proof_ns)
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
      let uu___124_5619 = env in
      {
        solver = (uu___124_5619.solver);
        range = (uu___124_5619.range);
        curmodule = (uu___124_5619.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5619.gamma_cache);
        modules = (uu___124_5619.modules);
        expected_typ = (uu___124_5619.expected_typ);
        sigtab = (uu___124_5619.sigtab);
        is_pattern = (uu___124_5619.is_pattern);
        instantiate_imp = (uu___124_5619.instantiate_imp);
        effects = (uu___124_5619.effects);
        generalize = (uu___124_5619.generalize);
        letrecs = (uu___124_5619.letrecs);
        top_level = (uu___124_5619.top_level);
        check_uvars = (uu___124_5619.check_uvars);
        use_eq = (uu___124_5619.use_eq);
        is_iface = (uu___124_5619.is_iface);
        admit = (uu___124_5619.admit);
        lax = (uu___124_5619.lax);
        lax_universes = (uu___124_5619.lax_universes);
        type_of = (uu___124_5619.type_of);
        universe_of = (uu___124_5619.universe_of);
        use_bv_sorts = (uu___124_5619.use_bv_sorts);
        qname_and_index = (uu___124_5619.qname_and_index);
        proof_ns = (uu___124_5619.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5640 = env in
             {
               solver = (uu___125_5640.solver);
               range = (uu___125_5640.range);
               curmodule = (uu___125_5640.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5640.gamma_cache);
               modules = (uu___125_5640.modules);
               expected_typ = (uu___125_5640.expected_typ);
               sigtab = (uu___125_5640.sigtab);
               is_pattern = (uu___125_5640.is_pattern);
               instantiate_imp = (uu___125_5640.instantiate_imp);
               effects = (uu___125_5640.effects);
               generalize = (uu___125_5640.generalize);
               letrecs = (uu___125_5640.letrecs);
               top_level = (uu___125_5640.top_level);
               check_uvars = (uu___125_5640.check_uvars);
               use_eq = (uu___125_5640.use_eq);
               is_iface = (uu___125_5640.is_iface);
               admit = (uu___125_5640.admit);
               lax = (uu___125_5640.lax);
               lax_universes = (uu___125_5640.lax_universes);
               type_of = (uu___125_5640.type_of);
               universe_of = (uu___125_5640.universe_of);
               use_bv_sorts = (uu___125_5640.use_bv_sorts);
               qname_and_index = (uu___125_5640.qname_and_index);
               proof_ns = (uu___125_5640.proof_ns)
             }))
    | uu____5641 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5654  ->
             match uu____5654 with | (x,uu____5658) -> push_bv env1 x) env bs
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
            let uu___126_5678 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5678.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5678.FStar_Syntax_Syntax.index);
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
      (let uu___127_5708 = env in
       {
         solver = (uu___127_5708.solver);
         range = (uu___127_5708.range);
         curmodule = (uu___127_5708.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5708.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5708.sigtab);
         is_pattern = (uu___127_5708.is_pattern);
         instantiate_imp = (uu___127_5708.instantiate_imp);
         effects = (uu___127_5708.effects);
         generalize = (uu___127_5708.generalize);
         letrecs = (uu___127_5708.letrecs);
         top_level = (uu___127_5708.top_level);
         check_uvars = (uu___127_5708.check_uvars);
         use_eq = (uu___127_5708.use_eq);
         is_iface = (uu___127_5708.is_iface);
         admit = (uu___127_5708.admit);
         lax = (uu___127_5708.lax);
         lax_universes = (uu___127_5708.lax_universes);
         type_of = (uu___127_5708.type_of);
         universe_of = (uu___127_5708.universe_of);
         use_bv_sorts = (uu___127_5708.use_bv_sorts);
         qname_and_index = (uu___127_5708.qname_and_index);
         proof_ns = (uu___127_5708.proof_ns)
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
        let uu____5732 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5732 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5748 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5748)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5758 = env in
      {
        solver = (uu___128_5758.solver);
        range = (uu___128_5758.range);
        curmodule = (uu___128_5758.curmodule);
        gamma = (uu___128_5758.gamma);
        gamma_cache = (uu___128_5758.gamma_cache);
        modules = (uu___128_5758.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5758.sigtab);
        is_pattern = (uu___128_5758.is_pattern);
        instantiate_imp = (uu___128_5758.instantiate_imp);
        effects = (uu___128_5758.effects);
        generalize = (uu___128_5758.generalize);
        letrecs = (uu___128_5758.letrecs);
        top_level = (uu___128_5758.top_level);
        check_uvars = (uu___128_5758.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5758.is_iface);
        admit = (uu___128_5758.admit);
        lax = (uu___128_5758.lax);
        lax_universes = (uu___128_5758.lax_universes);
        type_of = (uu___128_5758.type_of);
        universe_of = (uu___128_5758.universe_of);
        use_bv_sorts = (uu___128_5758.use_bv_sorts);
        qname_and_index = (uu___128_5758.qname_and_index);
        proof_ns = (uu___128_5758.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5774 = expected_typ env_ in
    ((let uu___129_5777 = env_ in
      {
        solver = (uu___129_5777.solver);
        range = (uu___129_5777.range);
        curmodule = (uu___129_5777.curmodule);
        gamma = (uu___129_5777.gamma);
        gamma_cache = (uu___129_5777.gamma_cache);
        modules = (uu___129_5777.modules);
        expected_typ = None;
        sigtab = (uu___129_5777.sigtab);
        is_pattern = (uu___129_5777.is_pattern);
        instantiate_imp = (uu___129_5777.instantiate_imp);
        effects = (uu___129_5777.effects);
        generalize = (uu___129_5777.generalize);
        letrecs = (uu___129_5777.letrecs);
        top_level = (uu___129_5777.top_level);
        check_uvars = (uu___129_5777.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5777.is_iface);
        admit = (uu___129_5777.admit);
        lax = (uu___129_5777.lax);
        lax_universes = (uu___129_5777.lax_universes);
        type_of = (uu___129_5777.type_of);
        universe_of = (uu___129_5777.universe_of);
        use_bv_sorts = (uu___129_5777.use_bv_sorts);
        qname_and_index = (uu___129_5777.qname_and_index);
        proof_ns = (uu___129_5777.proof_ns)
      }), uu____5774)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5788 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5792  ->
                    match uu___108_5792 with
                    | Binding_sig (uu____5794,se) -> [se]
                    | uu____5798 -> [])) in
          FStar_All.pipe_right uu____5788 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5803 = env in
       {
         solver = (uu___130_5803.solver);
         range = (uu___130_5803.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5803.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5803.expected_typ);
         sigtab = (uu___130_5803.sigtab);
         is_pattern = (uu___130_5803.is_pattern);
         instantiate_imp = (uu___130_5803.instantiate_imp);
         effects = (uu___130_5803.effects);
         generalize = (uu___130_5803.generalize);
         letrecs = (uu___130_5803.letrecs);
         top_level = (uu___130_5803.top_level);
         check_uvars = (uu___130_5803.check_uvars);
         use_eq = (uu___130_5803.use_eq);
         is_iface = (uu___130_5803.is_iface);
         admit = (uu___130_5803.admit);
         lax = (uu___130_5803.lax);
         lax_universes = (uu___130_5803.lax_universes);
         type_of = (uu___130_5803.type_of);
         universe_of = (uu___130_5803.universe_of);
         use_bv_sorts = (uu___130_5803.use_bv_sorts);
         qname_and_index = (uu___130_5803.qname_and_index);
         proof_ns = (uu___130_5803.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5853)::tl1 -> aux out tl1
      | (Binding_lid (uu____5856,(uu____5857,t)))::tl1 ->
          let uu____5866 =
            let uu____5870 = FStar_Syntax_Free.uvars t in ext out uu____5870 in
          aux uu____5866 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5874;
            FStar_Syntax_Syntax.index = uu____5875;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5881 =
            let uu____5885 = FStar_Syntax_Free.uvars t in ext out uu____5885 in
          aux uu____5881 tl1
      | (Binding_sig uu____5889)::uu____5890 -> out
      | (Binding_sig_inst uu____5895)::uu____5896 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5933)::tl1 -> aux out tl1
      | (Binding_univ uu____5940)::tl1 -> aux out tl1
      | (Binding_lid (uu____5943,(uu____5944,t)))::tl1 ->
          let uu____5953 =
            let uu____5955 = FStar_Syntax_Free.univs t in ext out uu____5955 in
          aux uu____5953 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5957;
            FStar_Syntax_Syntax.index = uu____5958;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5964 =
            let uu____5966 = FStar_Syntax_Free.univs t in ext out uu____5966 in
          aux uu____5964 tl1
      | (Binding_sig uu____5968)::uu____5969 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6006)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6016 = FStar_Util.set_add uname out in aux uu____6016 tl1
      | (Binding_lid (uu____6018,(uu____6019,t)))::tl1 ->
          let uu____6028 =
            let uu____6030 = FStar_Syntax_Free.univnames t in
            ext out uu____6030 in
          aux uu____6028 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6032;
            FStar_Syntax_Syntax.index = uu____6033;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6039 =
            let uu____6041 = FStar_Syntax_Free.univnames t in
            ext out uu____6041 in
          aux uu____6039 tl1
      | (Binding_sig uu____6043)::uu____6044 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6060  ->
            match uu___109_6060 with
            | Binding_var x -> [x]
            | Binding_lid uu____6063 -> []
            | Binding_sig uu____6066 -> []
            | Binding_univ uu____6070 -> []
            | Binding_sig_inst uu____6071 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6081 =
      let uu____6083 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6083
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6081 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6099 =
      let uu____6100 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6104  ->
                match uu___110_6104 with
                | Binding_var x ->
                    let uu____6106 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6106
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6109) ->
                    let uu____6110 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6110
                | Binding_sig (ls,uu____6112) ->
                    let uu____6115 =
                      let uu____6116 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6116
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6115
                | Binding_sig_inst (ls,uu____6122,uu____6123) ->
                    let uu____6126 =
                      let uu____6127 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6127
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6126)) in
      FStar_All.pipe_right uu____6100 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6099 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6139 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6139
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6160  ->
                 fun uu____6161  ->
                   match (uu____6160, uu____6161) with
                   | ((b1,uu____6171),(b2,uu____6173)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6216  ->
             match uu___111_6216 with
             | Binding_sig (lids,uu____6220) -> FStar_List.append lids keys
             | uu____6223 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6225  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6250) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6262,uu____6263) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6287 = list_prefix p path1 in
            if uu____6287 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6297 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6297
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6317 = e in
            {
              solver = (uu___131_6317.solver);
              range = (uu___131_6317.range);
              curmodule = (uu___131_6317.curmodule);
              gamma = (uu___131_6317.gamma);
              gamma_cache = (uu___131_6317.gamma_cache);
              modules = (uu___131_6317.modules);
              expected_typ = (uu___131_6317.expected_typ);
              sigtab = (uu___131_6317.sigtab);
              is_pattern = (uu___131_6317.is_pattern);
              instantiate_imp = (uu___131_6317.instantiate_imp);
              effects = (uu___131_6317.effects);
              generalize = (uu___131_6317.generalize);
              letrecs = (uu___131_6317.letrecs);
              top_level = (uu___131_6317.top_level);
              check_uvars = (uu___131_6317.check_uvars);
              use_eq = (uu___131_6317.use_eq);
              is_iface = (uu___131_6317.is_iface);
              admit = (uu___131_6317.admit);
              lax = (uu___131_6317.lax);
              lax_universes = (uu___131_6317.lax_universes);
              type_of = (uu___131_6317.type_of);
              universe_of = (uu___131_6317.universe_of);
              use_bv_sorts = (uu___131_6317.use_bv_sorts);
              qname_and_index = (uu___131_6317.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6336 = e in
    {
      solver = (uu___132_6336.solver);
      range = (uu___132_6336.range);
      curmodule = (uu___132_6336.curmodule);
      gamma = (uu___132_6336.gamma);
      gamma_cache = (uu___132_6336.gamma_cache);
      modules = (uu___132_6336.modules);
      expected_typ = (uu___132_6336.expected_typ);
      sigtab = (uu___132_6336.sigtab);
      is_pattern = (uu___132_6336.is_pattern);
      instantiate_imp = (uu___132_6336.instantiate_imp);
      effects = (uu___132_6336.effects);
      generalize = (uu___132_6336.generalize);
      letrecs = (uu___132_6336.letrecs);
      top_level = (uu___132_6336.top_level);
      check_uvars = (uu___132_6336.check_uvars);
      use_eq = (uu___132_6336.use_eq);
      is_iface = (uu___132_6336.is_iface);
      admit = (uu___132_6336.admit);
      lax = (uu___132_6336.lax);
      lax_universes = (uu___132_6336.lax_universes);
      type_of = (uu___132_6336.type_of);
      universe_of = (uu___132_6336.universe_of);
      use_bv_sorts = (uu___132_6336.use_bv_sorts);
      qname_and_index = (uu___132_6336.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6345::rest ->
        let uu___133_6348 = e in
        {
          solver = (uu___133_6348.solver);
          range = (uu___133_6348.range);
          curmodule = (uu___133_6348.curmodule);
          gamma = (uu___133_6348.gamma);
          gamma_cache = (uu___133_6348.gamma_cache);
          modules = (uu___133_6348.modules);
          expected_typ = (uu___133_6348.expected_typ);
          sigtab = (uu___133_6348.sigtab);
          is_pattern = (uu___133_6348.is_pattern);
          instantiate_imp = (uu___133_6348.instantiate_imp);
          effects = (uu___133_6348.effects);
          generalize = (uu___133_6348.generalize);
          letrecs = (uu___133_6348.letrecs);
          top_level = (uu___133_6348.top_level);
          check_uvars = (uu___133_6348.check_uvars);
          use_eq = (uu___133_6348.use_eq);
          is_iface = (uu___133_6348.is_iface);
          admit = (uu___133_6348.admit);
          lax = (uu___133_6348.lax);
          lax_universes = (uu___133_6348.lax_universes);
          type_of = (uu___133_6348.type_of);
          universe_of = (uu___133_6348.universe_of);
          use_bv_sorts = (uu___133_6348.use_bv_sorts);
          qname_and_index = (uu___133_6348.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6358 = e in
      {
        solver = (uu___134_6358.solver);
        range = (uu___134_6358.range);
        curmodule = (uu___134_6358.curmodule);
        gamma = (uu___134_6358.gamma);
        gamma_cache = (uu___134_6358.gamma_cache);
        modules = (uu___134_6358.modules);
        expected_typ = (uu___134_6358.expected_typ);
        sigtab = (uu___134_6358.sigtab);
        is_pattern = (uu___134_6358.is_pattern);
        instantiate_imp = (uu___134_6358.instantiate_imp);
        effects = (uu___134_6358.effects);
        generalize = (uu___134_6358.generalize);
        letrecs = (uu___134_6358.letrecs);
        top_level = (uu___134_6358.top_level);
        check_uvars = (uu___134_6358.check_uvars);
        use_eq = (uu___134_6358.use_eq);
        is_iface = (uu___134_6358.is_iface);
        admit = (uu___134_6358.admit);
        lax = (uu___134_6358.lax);
        lax_universes = (uu___134_6358.lax_universes);
        type_of = (uu___134_6358.type_of);
        universe_of = (uu___134_6358.universe_of);
        use_bv_sorts = (uu___134_6358.use_bv_sorts);
        qname_and_index = (uu___134_6358.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6376 =
        FStar_List.map
          (fun fpns  ->
             let uu____6387 =
               let uu____6388 =
                 let uu____6389 =
                   FStar_List.map
                     (fun uu____6394  ->
                        match uu____6394 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6389 in
               Prims.strcat uu____6388 "]" in
             Prims.strcat "[" uu____6387) pns in
      FStar_String.concat ";" uu____6376 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6403  -> ());
    push = (fun uu____6404  -> ());
    pop = (fun uu____6405  -> ());
    mark = (fun uu____6406  -> ());
    reset_mark = (fun uu____6407  -> ());
    commit_mark = (fun uu____6408  -> ());
    encode_modul = (fun uu____6409  -> fun uu____6410  -> ());
    encode_sig = (fun uu____6411  -> fun uu____6412  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6419  -> fun uu____6420  -> fun uu____6421  -> ());
    is_trivial = (fun uu____6425  -> fun uu____6426  -> false);
    finish = (fun uu____6427  -> ());
    refresh = (fun uu____6428  -> ())
  }