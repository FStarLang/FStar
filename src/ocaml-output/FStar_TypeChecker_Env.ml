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
          let uu____1445 = FStar_Syntax_Subst.subst vs t in (us, uu____1445)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1450  ->
    match uu___100_1450 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1464  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1474 = inst_tscheme t in
      match uu____1474 with
      | (us,t1) ->
          let uu____1481 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1481)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1493  ->
          match uu____1493 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1507 =
                         let uu____1508 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1511 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1514 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1515 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1508 uu____1511 uu____1514 uu____1515 in
                       failwith uu____1507)
                    else ();
                    (let uu____1517 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1517))
               | uu____1521 ->
                   let uu____1522 =
                     let uu____1523 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1523 in
                   failwith uu____1522)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1527 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1531 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1535 -> false
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
             | ([],uu____1561) -> Maybe
             | (uu____1565,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1577 -> No in
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
          let uu____1637 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1637 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1658  ->
                   match uu___101_1658 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1681 =
                           let uu____1691 =
                             let uu____1699 = inst_tscheme t in
                             FStar_Util.Inl uu____1699 in
                           (uu____1691, (FStar_Ident.range_of_lid l)) in
                         Some uu____1681
                       else None
                   | Binding_sig
                       (uu____1733,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1735);
                                     FStar_Syntax_Syntax.sigrng = uu____1736;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1737;
                                     FStar_Syntax_Syntax.sigmeta = uu____1738;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1747 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1747
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1774 ->
                             Some t
                         | uu____1778 -> cache t in
                       let uu____1779 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1779 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1819 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1819 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1863 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1905 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1905
         then
           let uu____1916 = find_in_sigtab env lid in
           match uu____1916 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1982) ->
          add_sigelts env ses
      | uu____1987 ->
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
            | uu____1996 -> ()))
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
        (fun uu___102_2014  ->
           match uu___102_2014 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2027 -> None)
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
          ((uu____2048,lb::[]),uu____2050,uu____2051) ->
          let uu____2060 =
            let uu____2065 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2071 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2065, uu____2071) in
          Some uu____2060
      | FStar_Syntax_Syntax.Sig_let ((uu____2078,lbs),uu____2080,uu____2081)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2101 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2108 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2108
                   then
                     let uu____2114 =
                       let uu____2119 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2125 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2119, uu____2125) in
                     Some uu____2114
                   else None)
      | uu____2137 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2156 =
          let uu____2161 =
            let uu____2164 =
              let uu____2165 =
                let uu____2168 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2168 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2165) in
            inst_tscheme uu____2164 in
          (uu____2161, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2156
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2182,uu____2183) ->
        let uu____2186 =
          let uu____2191 =
            let uu____2194 =
              let uu____2195 =
                let uu____2198 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2198 in
              (us, uu____2195) in
            inst_tscheme uu____2194 in
          (uu____2191, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2186
    | uu____2209 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2244 =
        match uu____2244 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2294,uvs,t,uu____2297,uu____2298,uu____2299);
                    FStar_Syntax_Syntax.sigrng = uu____2300;
                    FStar_Syntax_Syntax.sigquals = uu____2301;
                    FStar_Syntax_Syntax.sigmeta = uu____2302;_},None
                  )
                 ->
                 let uu____2312 =
                   let uu____2317 = inst_tscheme (uvs, t) in
                   (uu____2317, rng) in
                 Some uu____2312
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2329;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2331;_},None
                  )
                 ->
                 let uu____2339 =
                   let uu____2340 = in_cur_mod env l in uu____2340 = Yes in
                 if uu____2339
                 then
                   let uu____2346 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2346
                    then
                      let uu____2353 =
                        let uu____2358 = inst_tscheme (uvs, t) in
                        (uu____2358, rng) in
                      Some uu____2353
                    else None)
                 else
                   (let uu____2373 =
                      let uu____2378 = inst_tscheme (uvs, t) in
                      (uu____2378, rng) in
                    Some uu____2373)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2391,uu____2392);
                    FStar_Syntax_Syntax.sigrng = uu____2393;
                    FStar_Syntax_Syntax.sigquals = uu____2394;
                    FStar_Syntax_Syntax.sigmeta = uu____2395;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2414 =
                        let uu____2419 = inst_tscheme (uvs, k) in
                        (uu____2419, rng) in
                      Some uu____2414
                  | uu____2428 ->
                      let uu____2429 =
                        let uu____2434 =
                          let uu____2437 =
                            let uu____2438 =
                              let uu____2441 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2441 in
                            (uvs, uu____2438) in
                          inst_tscheme uu____2437 in
                        (uu____2434, rng) in
                      Some uu____2429)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2456,uu____2457);
                    FStar_Syntax_Syntax.sigrng = uu____2458;
                    FStar_Syntax_Syntax.sigquals = uu____2459;
                    FStar_Syntax_Syntax.sigmeta = uu____2460;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2480 =
                        let uu____2485 = inst_tscheme_with (uvs, k) us in
                        (uu____2485, rng) in
                      Some uu____2480
                  | uu____2494 ->
                      let uu____2495 =
                        let uu____2500 =
                          let uu____2503 =
                            let uu____2504 =
                              let uu____2507 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2507 in
                            (uvs, uu____2504) in
                          inst_tscheme_with uu____2503 us in
                        (uu____2500, rng) in
                      Some uu____2495)
             | FStar_Util.Inr se ->
                 let uu____2527 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2538;
                        FStar_Syntax_Syntax.sigrng = uu____2539;
                        FStar_Syntax_Syntax.sigquals = uu____2540;
                        FStar_Syntax_Syntax.sigmeta = uu____2541;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2550 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2527
                   (FStar_Util.map_option
                      (fun uu____2573  ->
                         match uu____2573 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2590 =
        let uu____2596 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2596 mapper in
      match uu____2590 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2648 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2648.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2648.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2648.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2669 = lookup_qname env l in
      match uu____2669 with | None  -> false | Some uu____2689 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2717 = try_lookup_bv env bv in
      match uu____2717 with
      | None  ->
          let uu____2725 =
            let uu____2726 =
              let uu____2729 = variable_not_found bv in (uu____2729, bvr) in
            FStar_Errors.Error uu____2726 in
          raise uu____2725
      | Some (t,r) ->
          let uu____2736 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2737 = FStar_Range.set_use_range r bvr in
          (uu____2736, uu____2737)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2749 = try_lookup_lid_aux env l in
      match uu____2749 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2791 =
            let uu____2796 =
              let uu____2799 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2799) in
            (uu____2796, r1) in
          Some uu____2791
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2816 = try_lookup_lid env l in
      match uu____2816 with
      | None  ->
          let uu____2830 =
            let uu____2831 =
              let uu____2834 = name_not_found l in
              (uu____2834, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2831 in
          raise uu____2830
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2855  ->
              match uu___103_2855 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2857 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2868 = lookup_qname env lid in
      match uu____2868 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2883,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2886;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2888;_},None
            ),uu____2889)
          ->
          let uu____2913 =
            let uu____2919 =
              let uu____2922 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2922) in
            (uu____2919, q) in
          Some uu____2913
      | uu____2931 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2953 = lookup_qname env lid in
      match uu____2953 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2966,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2969;
              FStar_Syntax_Syntax.sigquals = uu____2970;
              FStar_Syntax_Syntax.sigmeta = uu____2971;_},None
            ),uu____2972)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2996 ->
          let uu____3007 =
            let uu____3008 =
              let uu____3011 = name_not_found lid in
              (uu____3011, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3008 in
          raise uu____3007
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3022 = lookup_qname env lid in
      match uu____3022 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3035,uvs,t,uu____3038,uu____3039,uu____3040);
              FStar_Syntax_Syntax.sigrng = uu____3041;
              FStar_Syntax_Syntax.sigquals = uu____3042;
              FStar_Syntax_Syntax.sigmeta = uu____3043;_},None
            ),uu____3044)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3070 ->
          let uu____3081 =
            let uu____3082 =
              let uu____3085 = name_not_found lid in
              (uu____3085, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3082 in
          raise uu____3081
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3097 = lookup_qname env lid in
      match uu____3097 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3111,uu____3112,uu____3113,uu____3114,uu____3115,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3117;
              FStar_Syntax_Syntax.sigquals = uu____3118;
              FStar_Syntax_Syntax.sigmeta = uu____3119;_},uu____3120),uu____3121)
          -> (true, dcs)
      | uu____3151 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3169 = lookup_qname env lid in
      match uu____3169 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3180,uu____3181,uu____3182,l,uu____3184,uu____3185);
              FStar_Syntax_Syntax.sigrng = uu____3186;
              FStar_Syntax_Syntax.sigquals = uu____3187;
              FStar_Syntax_Syntax.sigmeta = uu____3188;_},uu____3189),uu____3190)
          -> l
      | uu____3217 ->
          let uu____3228 =
            let uu____3229 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3229 in
          failwith uu____3228
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
        let uu____3253 = lookup_qname env lid in
        match uu____3253 with
        | Some (FStar_Util.Inr (se,None ),uu____3268) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3294,lbs),uu____3296,uu____3297) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3314 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3314
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3335 -> None)
        | uu____3338 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3359 = lookup_qname env ftv in
      match uu____3359 with
      | Some (FStar_Util.Inr (se,None ),uu____3372) ->
          let uu____3395 = effect_signature se in
          (match uu____3395 with
           | None  -> None
           | Some ((uu____3406,t),r) ->
               let uu____3415 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3415)
      | uu____3416 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3433 = try_lookup_effect_lid env ftv in
      match uu____3433 with
      | None  ->
          let uu____3435 =
            let uu____3436 =
              let uu____3439 = name_not_found ftv in
              (uu____3439, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3436 in
          raise uu____3435
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
        let uu____3453 = lookup_qname env lid0 in
        match uu____3453 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3471);
                FStar_Syntax_Syntax.sigrng = uu____3472;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3474;_},None
              ),uu____3475)
            ->
            let lid1 =
              let uu____3502 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3502 in
            let uu____3503 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3505  ->
                      match uu___104_3505 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3506 -> false)) in
            if uu____3503
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
                     (let uu____3522 =
                        let uu____3523 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3524 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3523 uu____3524 in
                      failwith uu____3522) in
               match (binders, univs1) with
               | ([],uu____3530) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3539,uu____3540::uu____3541::uu____3542) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3545 =
                     let uu____3546 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3547 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3546 uu____3547 in
                   failwith uu____3545
               | uu____3553 ->
                   let uu____3556 =
                     let uu____3559 =
                       let uu____3560 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3560) in
                     inst_tscheme_with uu____3559 insts in
                   (match uu____3556 with
                    | (uu____3568,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3571 =
                          let uu____3572 = FStar_Syntax_Subst.compress t1 in
                          uu____3572.FStar_Syntax_Syntax.n in
                        (match uu____3571 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3602 -> failwith "Impossible")))
        | uu____3606 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3632 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3632 with
        | None  -> None
        | Some (uu____3639,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3644 = find1 l2 in
            (match uu____3644 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3649 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3649 with
        | Some l1 -> l1
        | None  ->
            let uu____3652 = find1 l in
            (match uu____3652 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3664 = lookup_qname env l1 in
      match uu____3664 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3676;
              FStar_Syntax_Syntax.sigrng = uu____3677;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3679;_},uu____3680),uu____3681)
          -> q
      | uu____3706 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3729 =
          let uu____3730 =
            let uu____3731 = FStar_Util.string_of_int i in
            let uu____3732 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3731 uu____3732 in
          failwith uu____3730 in
        let uu____3733 = lookup_datacon env lid in
        match uu____3733 with
        | (uu____3736,t) ->
            let uu____3738 =
              let uu____3739 = FStar_Syntax_Subst.compress t in
              uu____3739.FStar_Syntax_Syntax.n in
            (match uu____3738 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3743) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3764 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3764 FStar_Pervasives.fst)
             | uu____3769 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3776 = lookup_qname env l in
      match uu____3776 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3787,uu____3788,uu____3789);
              FStar_Syntax_Syntax.sigrng = uu____3790;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3792;_},uu____3793),uu____3794)
          ->
          FStar_Util.for_some
            (fun uu___105_3819  ->
               match uu___105_3819 with
               | FStar_Syntax_Syntax.Projector uu____3820 -> true
               | uu____3823 -> false) quals
      | uu____3824 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3841 = lookup_qname env lid in
      match uu____3841 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3852,uu____3853,uu____3854,uu____3855,uu____3856,uu____3857);
              FStar_Syntax_Syntax.sigrng = uu____3858;
              FStar_Syntax_Syntax.sigquals = uu____3859;
              FStar_Syntax_Syntax.sigmeta = uu____3860;_},uu____3861),uu____3862)
          -> true
      | uu____3889 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3906 = lookup_qname env lid in
      match uu____3906 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3917,uu____3918,uu____3919,uu____3920,uu____3921,uu____3922);
              FStar_Syntax_Syntax.sigrng = uu____3923;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3925;_},uu____3926),uu____3927)
          ->
          FStar_Util.for_some
            (fun uu___106_3956  ->
               match uu___106_3956 with
               | FStar_Syntax_Syntax.RecordType uu____3957 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3962 -> true
               | uu____3967 -> false) quals
      | uu____3968 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3985 = lookup_qname env lid in
      match uu____3985 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3996,uu____3997,uu____3998);
              FStar_Syntax_Syntax.sigrng = uu____3999;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4001;_},uu____4002),uu____4003)
          ->
          FStar_Util.for_some
            (fun uu___107_4032  ->
               match uu___107_4032 with
               | FStar_Syntax_Syntax.Action uu____4033 -> true
               | uu____4034 -> false) quals
      | uu____4035 -> false
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
      let uu____4054 =
        let uu____4055 = FStar_Syntax_Util.un_uinst head1 in
        uu____4055.FStar_Syntax_Syntax.n in
      match uu____4054 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4059 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4097 -> Some false
        | FStar_Util.Inr (se,uu____4106) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4115 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4119 -> Some true
             | uu____4128 -> Some false) in
      let uu____4129 =
        let uu____4131 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4131 mapper in
      match uu____4129 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4158 = lookup_qname env lid in
      match uu____4158 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4169,uu____4170,tps,uu____4172,uu____4173,uu____4174);
              FStar_Syntax_Syntax.sigrng = uu____4175;
              FStar_Syntax_Syntax.sigquals = uu____4176;
              FStar_Syntax_Syntax.sigmeta = uu____4177;_},uu____4178),uu____4179)
          -> FStar_List.length tps
      | uu____4211 ->
          let uu____4222 =
            let uu____4223 =
              let uu____4226 = name_not_found lid in
              (uu____4226, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4223 in
          raise uu____4222
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
           (fun uu____4248  ->
              match uu____4248 with
              | (d,uu____4253) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4262 = effect_decl_opt env l in
      match uu____4262 with
      | None  ->
          let uu____4270 =
            let uu____4271 =
              let uu____4274 = name_not_found l in
              (uu____4274, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4271 in
          raise uu____4270
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
            (let uu____4317 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4341  ->
                       match uu____4341 with
                       | (m1,m2,uu____4349,uu____4350,uu____4351) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4317 with
             | None  ->
                 let uu____4360 =
                   let uu____4361 =
                     let uu____4364 =
                       let uu____4365 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4366 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4365
                         uu____4366 in
                     (uu____4364, (env.range)) in
                   FStar_Errors.Error uu____4361 in
                 raise uu____4360
             | Some (uu____4370,uu____4371,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4418 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4430  ->
            match uu____4430 with
            | (d,uu____4434) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4418 with
  | None  ->
      let uu____4441 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4441
  | Some (md,_q) ->
      let uu____4450 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4450 with
       | (uu____4457,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4465)::(wp,uu____4467)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4489 -> failwith "Impossible"))
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
                 let uu____4525 = get_range env in
                 let uu____4526 =
                   let uu____4529 =
                     let uu____4530 =
                       let uu____4540 =
                         let uu____4542 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4542] in
                       (null_wp, uu____4540) in
                     FStar_Syntax_Syntax.Tm_app uu____4530 in
                   FStar_Syntax_Syntax.mk uu____4529 in
                 uu____4526 None uu____4525 in
               let uu____4552 =
                 let uu____4553 =
                   let uu____4559 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4559] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4553;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4552)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4568 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4568.order);
              joins = (uu___118_4568.joins)
            } in
          let uu___119_4573 = env in
          {
            solver = (uu___119_4573.solver);
            range = (uu___119_4573.range);
            curmodule = (uu___119_4573.curmodule);
            gamma = (uu___119_4573.gamma);
            gamma_cache = (uu___119_4573.gamma_cache);
            modules = (uu___119_4573.modules);
            expected_typ = (uu___119_4573.expected_typ);
            sigtab = (uu___119_4573.sigtab);
            is_pattern = (uu___119_4573.is_pattern);
            instantiate_imp = (uu___119_4573.instantiate_imp);
            effects;
            generalize = (uu___119_4573.generalize);
            letrecs = (uu___119_4573.letrecs);
            top_level = (uu___119_4573.top_level);
            check_uvars = (uu___119_4573.check_uvars);
            use_eq = (uu___119_4573.use_eq);
            is_iface = (uu___119_4573.is_iface);
            admit = (uu___119_4573.admit);
            lax = (uu___119_4573.lax);
            lax_universes = (uu___119_4573.lax_universes);
            type_of = (uu___119_4573.type_of);
            universe_of = (uu___119_4573.universe_of);
            use_bv_sorts = (uu___119_4573.use_bv_sorts);
            qname_and_index = (uu___119_4573.qname_and_index);
            proof_ns = (uu___119_4573.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4590 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4590 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4669 = (e1.mlift).mlift_wp t wp in
                              let uu____4670 = l1 t wp e in
                              l2 t uu____4669 uu____4670))
                | uu____4671 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4706 = inst_tscheme lift_t in
            match uu____4706 with
            | (uu____4711,lift_t1) ->
                let uu____4713 =
                  let uu____4716 =
                    let uu____4717 =
                      let uu____4727 =
                        let uu____4729 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4730 =
                          let uu____4732 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4732] in
                        uu____4729 :: uu____4730 in
                      (lift_t1, uu____4727) in
                    FStar_Syntax_Syntax.Tm_app uu____4717 in
                  FStar_Syntax_Syntax.mk uu____4716 in
                uu____4713 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4777 = inst_tscheme lift_t in
            match uu____4777 with
            | (uu____4782,lift_t1) ->
                let uu____4784 =
                  let uu____4787 =
                    let uu____4788 =
                      let uu____4798 =
                        let uu____4800 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4801 =
                          let uu____4803 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4804 =
                            let uu____4806 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4806] in
                          uu____4803 :: uu____4804 in
                        uu____4800 :: uu____4801 in
                      (lift_t1, uu____4798) in
                    FStar_Syntax_Syntax.Tm_app uu____4788 in
                  FStar_Syntax_Syntax.mk uu____4787 in
                uu____4784 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4847 =
                let uu____4848 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4848
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4847 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4852 =
              let uu____4853 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4853 in
            let uu____4854 =
              let uu____4855 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4870 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4870) in
              FStar_Util.dflt "none" uu____4855 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4852
              uu____4854 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4883  ->
                    match uu____4883 with
                    | (e,uu____4888) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4901 =
            match uu____4901 with
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
              let uu____4926 =
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
                                    (let uu____4938 =
                                       let uu____4943 =
                                         find_edge order1 (i, k) in
                                       let uu____4945 =
                                         find_edge order1 (k, j) in
                                       (uu____4943, uu____4945) in
                                     match uu____4938 with
                                     | (Some e1,Some e2) ->
                                         let uu____4954 = compose_edges e1 e2 in
                                         [uu____4954]
                                     | uu____4955 -> []))))) in
              FStar_List.append order1 uu____4926 in
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
                   let uu____4970 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4971 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4971
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4970
                   then
                     let uu____4974 =
                       let uu____4975 =
                         let uu____4978 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4979 = get_range env in
                         (uu____4978, uu____4979) in
                       FStar_Errors.Error uu____4975 in
                     raise uu____4974
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
                                            let uu____5042 =
                                              let uu____5047 =
                                                find_edge order2 (i, k) in
                                              let uu____5049 =
                                                find_edge order2 (j, k) in
                                              (uu____5047, uu____5049) in
                                            match uu____5042 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5072,uu____5073)
                                                     ->
                                                     let uu____5077 =
                                                       let uu____5080 =
                                                         let uu____5081 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5081 in
                                                       let uu____5083 =
                                                         let uu____5084 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5084 in
                                                       (uu____5080,
                                                         uu____5083) in
                                                     (match uu____5077 with
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
                                            | uu____5103 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5142 = env.effects in
              { decls = (uu___120_5142.decls); order = order2; joins } in
            let uu___121_5143 = env in
            {
              solver = (uu___121_5143.solver);
              range = (uu___121_5143.range);
              curmodule = (uu___121_5143.curmodule);
              gamma = (uu___121_5143.gamma);
              gamma_cache = (uu___121_5143.gamma_cache);
              modules = (uu___121_5143.modules);
              expected_typ = (uu___121_5143.expected_typ);
              sigtab = (uu___121_5143.sigtab);
              is_pattern = (uu___121_5143.is_pattern);
              instantiate_imp = (uu___121_5143.instantiate_imp);
              effects;
              generalize = (uu___121_5143.generalize);
              letrecs = (uu___121_5143.letrecs);
              top_level = (uu___121_5143.top_level);
              check_uvars = (uu___121_5143.check_uvars);
              use_eq = (uu___121_5143.use_eq);
              is_iface = (uu___121_5143.is_iface);
              admit = (uu___121_5143.admit);
              lax = (uu___121_5143.lax);
              lax_universes = (uu___121_5143.lax_universes);
              type_of = (uu___121_5143.type_of);
              universe_of = (uu___121_5143.universe_of);
              use_bv_sorts = (uu___121_5143.use_bv_sorts);
              qname_and_index = (uu___121_5143.qname_and_index);
              proof_ns = (uu___121_5143.proof_ns)
            }))
      | uu____5144 -> env
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
        | uu____5166 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5174 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5174 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5184 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5184 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5201 =
                     let uu____5202 =
                       let uu____5205 =
                         let uu____5206 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5212 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5220 =
                           let uu____5221 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5221 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5206 uu____5212 uu____5220 in
                       (uu____5205, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5202 in
                   raise uu____5201)
                else ();
                (let inst1 =
                   let uu____5225 =
                     let uu____5231 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5231 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5238  ->
                        fun uu____5239  ->
                          match (uu____5238, uu____5239) with
                          | ((x,uu____5253),(t,uu____5255)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5225 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5270 =
                     let uu___122_5271 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5271.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5271.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5271.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5271.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5270
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5301 =
    let uu____5306 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5306 in
  match uu____5301 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5322 =
        only_reifiable &&
          (let uu____5323 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5323) in
      if uu____5322
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5336 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5338 =
               let uu____5347 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5347) in
             (match uu____5338 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5381 =
                    let uu____5384 = get_range env in
                    let uu____5385 =
                      let uu____5388 =
                        let uu____5389 =
                          let uu____5399 =
                            let uu____5401 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5401; wp] in
                          (repr, uu____5399) in
                        FStar_Syntax_Syntax.Tm_app uu____5389 in
                      FStar_Syntax_Syntax.mk uu____5388 in
                    uu____5385 None uu____5384 in
                  Some uu____5381))
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
          let uu____5445 =
            let uu____5446 =
              let uu____5449 =
                let uu____5450 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5450 in
              let uu____5451 = get_range env in (uu____5449, uu____5451) in
            FStar_Errors.Error uu____5446 in
          raise uu____5445 in
        let uu____5452 = effect_repr_aux true env c u_c in
        match uu____5452 with
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
        | FStar_Util.Inr (eff_name,uu____5484) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5497 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5504 =
        let uu____5505 = FStar_Syntax_Subst.compress t in
        uu____5505.FStar_Syntax_Syntax.n in
      match uu____5504 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5508,c) ->
          is_reifiable_comp env c
      | uu____5520 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5538)::uu____5539 -> x :: rest
        | (Binding_sig_inst uu____5544)::uu____5545 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5554 = push1 x rest1 in local :: uu____5554 in
      let uu___123_5556 = env in
      let uu____5557 = push1 s env.gamma in
      {
        solver = (uu___123_5556.solver);
        range = (uu___123_5556.range);
        curmodule = (uu___123_5556.curmodule);
        gamma = uu____5557;
        gamma_cache = (uu___123_5556.gamma_cache);
        modules = (uu___123_5556.modules);
        expected_typ = (uu___123_5556.expected_typ);
        sigtab = (uu___123_5556.sigtab);
        is_pattern = (uu___123_5556.is_pattern);
        instantiate_imp = (uu___123_5556.instantiate_imp);
        effects = (uu___123_5556.effects);
        generalize = (uu___123_5556.generalize);
        letrecs = (uu___123_5556.letrecs);
        top_level = (uu___123_5556.top_level);
        check_uvars = (uu___123_5556.check_uvars);
        use_eq = (uu___123_5556.use_eq);
        is_iface = (uu___123_5556.is_iface);
        admit = (uu___123_5556.admit);
        lax = (uu___123_5556.lax);
        lax_universes = (uu___123_5556.lax_universes);
        type_of = (uu___123_5556.type_of);
        universe_of = (uu___123_5556.universe_of);
        use_bv_sorts = (uu___123_5556.use_bv_sorts);
        qname_and_index = (uu___123_5556.qname_and_index);
        proof_ns = (uu___123_5556.proof_ns)
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
      let uu___124_5584 = env in
      {
        solver = (uu___124_5584.solver);
        range = (uu___124_5584.range);
        curmodule = (uu___124_5584.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5584.gamma_cache);
        modules = (uu___124_5584.modules);
        expected_typ = (uu___124_5584.expected_typ);
        sigtab = (uu___124_5584.sigtab);
        is_pattern = (uu___124_5584.is_pattern);
        instantiate_imp = (uu___124_5584.instantiate_imp);
        effects = (uu___124_5584.effects);
        generalize = (uu___124_5584.generalize);
        letrecs = (uu___124_5584.letrecs);
        top_level = (uu___124_5584.top_level);
        check_uvars = (uu___124_5584.check_uvars);
        use_eq = (uu___124_5584.use_eq);
        is_iface = (uu___124_5584.is_iface);
        admit = (uu___124_5584.admit);
        lax = (uu___124_5584.lax);
        lax_universes = (uu___124_5584.lax_universes);
        type_of = (uu___124_5584.type_of);
        universe_of = (uu___124_5584.universe_of);
        use_bv_sorts = (uu___124_5584.use_bv_sorts);
        qname_and_index = (uu___124_5584.qname_and_index);
        proof_ns = (uu___124_5584.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5605 = env in
             {
               solver = (uu___125_5605.solver);
               range = (uu___125_5605.range);
               curmodule = (uu___125_5605.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5605.gamma_cache);
               modules = (uu___125_5605.modules);
               expected_typ = (uu___125_5605.expected_typ);
               sigtab = (uu___125_5605.sigtab);
               is_pattern = (uu___125_5605.is_pattern);
               instantiate_imp = (uu___125_5605.instantiate_imp);
               effects = (uu___125_5605.effects);
               generalize = (uu___125_5605.generalize);
               letrecs = (uu___125_5605.letrecs);
               top_level = (uu___125_5605.top_level);
               check_uvars = (uu___125_5605.check_uvars);
               use_eq = (uu___125_5605.use_eq);
               is_iface = (uu___125_5605.is_iface);
               admit = (uu___125_5605.admit);
               lax = (uu___125_5605.lax);
               lax_universes = (uu___125_5605.lax_universes);
               type_of = (uu___125_5605.type_of);
               universe_of = (uu___125_5605.universe_of);
               use_bv_sorts = (uu___125_5605.use_bv_sorts);
               qname_and_index = (uu___125_5605.qname_and_index);
               proof_ns = (uu___125_5605.proof_ns)
             }))
    | uu____5606 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5619  ->
             match uu____5619 with | (x,uu____5623) -> push_bv env1 x) env bs
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
            let uu___126_5643 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5643.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5643.FStar_Syntax_Syntax.index);
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
      (let uu___127_5673 = env in
       {
         solver = (uu___127_5673.solver);
         range = (uu___127_5673.range);
         curmodule = (uu___127_5673.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5673.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5673.sigtab);
         is_pattern = (uu___127_5673.is_pattern);
         instantiate_imp = (uu___127_5673.instantiate_imp);
         effects = (uu___127_5673.effects);
         generalize = (uu___127_5673.generalize);
         letrecs = (uu___127_5673.letrecs);
         top_level = (uu___127_5673.top_level);
         check_uvars = (uu___127_5673.check_uvars);
         use_eq = (uu___127_5673.use_eq);
         is_iface = (uu___127_5673.is_iface);
         admit = (uu___127_5673.admit);
         lax = (uu___127_5673.lax);
         lax_universes = (uu___127_5673.lax_universes);
         type_of = (uu___127_5673.type_of);
         universe_of = (uu___127_5673.universe_of);
         use_bv_sorts = (uu___127_5673.use_bv_sorts);
         qname_and_index = (uu___127_5673.qname_and_index);
         proof_ns = (uu___127_5673.proof_ns)
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
        let uu____5697 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5697 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5713 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5713)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5723 = env in
      {
        solver = (uu___128_5723.solver);
        range = (uu___128_5723.range);
        curmodule = (uu___128_5723.curmodule);
        gamma = (uu___128_5723.gamma);
        gamma_cache = (uu___128_5723.gamma_cache);
        modules = (uu___128_5723.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5723.sigtab);
        is_pattern = (uu___128_5723.is_pattern);
        instantiate_imp = (uu___128_5723.instantiate_imp);
        effects = (uu___128_5723.effects);
        generalize = (uu___128_5723.generalize);
        letrecs = (uu___128_5723.letrecs);
        top_level = (uu___128_5723.top_level);
        check_uvars = (uu___128_5723.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5723.is_iface);
        admit = (uu___128_5723.admit);
        lax = (uu___128_5723.lax);
        lax_universes = (uu___128_5723.lax_universes);
        type_of = (uu___128_5723.type_of);
        universe_of = (uu___128_5723.universe_of);
        use_bv_sorts = (uu___128_5723.use_bv_sorts);
        qname_and_index = (uu___128_5723.qname_and_index);
        proof_ns = (uu___128_5723.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5739 = expected_typ env_ in
    ((let uu___129_5742 = env_ in
      {
        solver = (uu___129_5742.solver);
        range = (uu___129_5742.range);
        curmodule = (uu___129_5742.curmodule);
        gamma = (uu___129_5742.gamma);
        gamma_cache = (uu___129_5742.gamma_cache);
        modules = (uu___129_5742.modules);
        expected_typ = None;
        sigtab = (uu___129_5742.sigtab);
        is_pattern = (uu___129_5742.is_pattern);
        instantiate_imp = (uu___129_5742.instantiate_imp);
        effects = (uu___129_5742.effects);
        generalize = (uu___129_5742.generalize);
        letrecs = (uu___129_5742.letrecs);
        top_level = (uu___129_5742.top_level);
        check_uvars = (uu___129_5742.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5742.is_iface);
        admit = (uu___129_5742.admit);
        lax = (uu___129_5742.lax);
        lax_universes = (uu___129_5742.lax_universes);
        type_of = (uu___129_5742.type_of);
        universe_of = (uu___129_5742.universe_of);
        use_bv_sorts = (uu___129_5742.use_bv_sorts);
        qname_and_index = (uu___129_5742.qname_and_index);
        proof_ns = (uu___129_5742.proof_ns)
      }), uu____5739)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5753 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5757  ->
                    match uu___108_5757 with
                    | Binding_sig (uu____5759,se) -> [se]
                    | uu____5763 -> [])) in
          FStar_All.pipe_right uu____5753 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5768 = env in
       {
         solver = (uu___130_5768.solver);
         range = (uu___130_5768.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5768.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5768.expected_typ);
         sigtab = (uu___130_5768.sigtab);
         is_pattern = (uu___130_5768.is_pattern);
         instantiate_imp = (uu___130_5768.instantiate_imp);
         effects = (uu___130_5768.effects);
         generalize = (uu___130_5768.generalize);
         letrecs = (uu___130_5768.letrecs);
         top_level = (uu___130_5768.top_level);
         check_uvars = (uu___130_5768.check_uvars);
         use_eq = (uu___130_5768.use_eq);
         is_iface = (uu___130_5768.is_iface);
         admit = (uu___130_5768.admit);
         lax = (uu___130_5768.lax);
         lax_universes = (uu___130_5768.lax_universes);
         type_of = (uu___130_5768.type_of);
         universe_of = (uu___130_5768.universe_of);
         use_bv_sorts = (uu___130_5768.use_bv_sorts);
         qname_and_index = (uu___130_5768.qname_and_index);
         proof_ns = (uu___130_5768.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5818)::tl1 -> aux out tl1
      | (Binding_lid (uu____5821,(uu____5822,t)))::tl1 ->
          let uu____5831 =
            let uu____5835 = FStar_Syntax_Free.uvars t in ext out uu____5835 in
          aux uu____5831 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5839;
            FStar_Syntax_Syntax.index = uu____5840;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5846 =
            let uu____5850 = FStar_Syntax_Free.uvars t in ext out uu____5850 in
          aux uu____5846 tl1
      | (Binding_sig uu____5854)::uu____5855 -> out
      | (Binding_sig_inst uu____5860)::uu____5861 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5898)::tl1 -> aux out tl1
      | (Binding_univ uu____5905)::tl1 -> aux out tl1
      | (Binding_lid (uu____5908,(uu____5909,t)))::tl1 ->
          let uu____5918 =
            let uu____5920 = FStar_Syntax_Free.univs t in ext out uu____5920 in
          aux uu____5918 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5922;
            FStar_Syntax_Syntax.index = uu____5923;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5929 =
            let uu____5931 = FStar_Syntax_Free.univs t in ext out uu____5931 in
          aux uu____5929 tl1
      | (Binding_sig uu____5933)::uu____5934 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5971)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5981 = FStar_Util.set_add uname out in aux uu____5981 tl1
      | (Binding_lid (uu____5983,(uu____5984,t)))::tl1 ->
          let uu____5993 =
            let uu____5995 = FStar_Syntax_Free.univnames t in
            ext out uu____5995 in
          aux uu____5993 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5997;
            FStar_Syntax_Syntax.index = uu____5998;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6004 =
            let uu____6006 = FStar_Syntax_Free.univnames t in
            ext out uu____6006 in
          aux uu____6004 tl1
      | (Binding_sig uu____6008)::uu____6009 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_6025  ->
            match uu___109_6025 with
            | Binding_var x -> [x]
            | Binding_lid uu____6028 -> []
            | Binding_sig uu____6031 -> []
            | Binding_univ uu____6035 -> []
            | Binding_sig_inst uu____6036 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6046 =
      let uu____6048 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6048
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6046 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6064 =
      let uu____6065 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6069  ->
                match uu___110_6069 with
                | Binding_var x ->
                    let uu____6071 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6071
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6074) ->
                    let uu____6075 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6075
                | Binding_sig (ls,uu____6077) ->
                    let uu____6080 =
                      let uu____6081 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6081
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6080
                | Binding_sig_inst (ls,uu____6087,uu____6088) ->
                    let uu____6091 =
                      let uu____6092 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6092
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6091)) in
      FStar_All.pipe_right uu____6065 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6064 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6104 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6104
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6121  ->
                 fun uu____6122  ->
                   match (uu____6121, uu____6122) with
                   | ((b1,uu____6132),(b2,uu____6134)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6177  ->
             match uu___111_6177 with
             | Binding_sig (lids,uu____6181) -> FStar_List.append lids keys
             | uu____6184 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6186  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6211) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6223,uu____6224) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6248 = list_prefix p path1 in
            if uu____6248 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6258 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6258
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6278 = e in
            {
              solver = (uu___131_6278.solver);
              range = (uu___131_6278.range);
              curmodule = (uu___131_6278.curmodule);
              gamma = (uu___131_6278.gamma);
              gamma_cache = (uu___131_6278.gamma_cache);
              modules = (uu___131_6278.modules);
              expected_typ = (uu___131_6278.expected_typ);
              sigtab = (uu___131_6278.sigtab);
              is_pattern = (uu___131_6278.is_pattern);
              instantiate_imp = (uu___131_6278.instantiate_imp);
              effects = (uu___131_6278.effects);
              generalize = (uu___131_6278.generalize);
              letrecs = (uu___131_6278.letrecs);
              top_level = (uu___131_6278.top_level);
              check_uvars = (uu___131_6278.check_uvars);
              use_eq = (uu___131_6278.use_eq);
              is_iface = (uu___131_6278.is_iface);
              admit = (uu___131_6278.admit);
              lax = (uu___131_6278.lax);
              lax_universes = (uu___131_6278.lax_universes);
              type_of = (uu___131_6278.type_of);
              universe_of = (uu___131_6278.universe_of);
              use_bv_sorts = (uu___131_6278.use_bv_sorts);
              qname_and_index = (uu___131_6278.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6297 = e in
    {
      solver = (uu___132_6297.solver);
      range = (uu___132_6297.range);
      curmodule = (uu___132_6297.curmodule);
      gamma = (uu___132_6297.gamma);
      gamma_cache = (uu___132_6297.gamma_cache);
      modules = (uu___132_6297.modules);
      expected_typ = (uu___132_6297.expected_typ);
      sigtab = (uu___132_6297.sigtab);
      is_pattern = (uu___132_6297.is_pattern);
      instantiate_imp = (uu___132_6297.instantiate_imp);
      effects = (uu___132_6297.effects);
      generalize = (uu___132_6297.generalize);
      letrecs = (uu___132_6297.letrecs);
      top_level = (uu___132_6297.top_level);
      check_uvars = (uu___132_6297.check_uvars);
      use_eq = (uu___132_6297.use_eq);
      is_iface = (uu___132_6297.is_iface);
      admit = (uu___132_6297.admit);
      lax = (uu___132_6297.lax);
      lax_universes = (uu___132_6297.lax_universes);
      type_of = (uu___132_6297.type_of);
      universe_of = (uu___132_6297.universe_of);
      use_bv_sorts = (uu___132_6297.use_bv_sorts);
      qname_and_index = (uu___132_6297.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6306::rest ->
        let uu___133_6309 = e in
        {
          solver = (uu___133_6309.solver);
          range = (uu___133_6309.range);
          curmodule = (uu___133_6309.curmodule);
          gamma = (uu___133_6309.gamma);
          gamma_cache = (uu___133_6309.gamma_cache);
          modules = (uu___133_6309.modules);
          expected_typ = (uu___133_6309.expected_typ);
          sigtab = (uu___133_6309.sigtab);
          is_pattern = (uu___133_6309.is_pattern);
          instantiate_imp = (uu___133_6309.instantiate_imp);
          effects = (uu___133_6309.effects);
          generalize = (uu___133_6309.generalize);
          letrecs = (uu___133_6309.letrecs);
          top_level = (uu___133_6309.top_level);
          check_uvars = (uu___133_6309.check_uvars);
          use_eq = (uu___133_6309.use_eq);
          is_iface = (uu___133_6309.is_iface);
          admit = (uu___133_6309.admit);
          lax = (uu___133_6309.lax);
          lax_universes = (uu___133_6309.lax_universes);
          type_of = (uu___133_6309.type_of);
          universe_of = (uu___133_6309.universe_of);
          use_bv_sorts = (uu___133_6309.use_bv_sorts);
          qname_and_index = (uu___133_6309.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6319 = e in
      {
        solver = (uu___134_6319.solver);
        range = (uu___134_6319.range);
        curmodule = (uu___134_6319.curmodule);
        gamma = (uu___134_6319.gamma);
        gamma_cache = (uu___134_6319.gamma_cache);
        modules = (uu___134_6319.modules);
        expected_typ = (uu___134_6319.expected_typ);
        sigtab = (uu___134_6319.sigtab);
        is_pattern = (uu___134_6319.is_pattern);
        instantiate_imp = (uu___134_6319.instantiate_imp);
        effects = (uu___134_6319.effects);
        generalize = (uu___134_6319.generalize);
        letrecs = (uu___134_6319.letrecs);
        top_level = (uu___134_6319.top_level);
        check_uvars = (uu___134_6319.check_uvars);
        use_eq = (uu___134_6319.use_eq);
        is_iface = (uu___134_6319.is_iface);
        admit = (uu___134_6319.admit);
        lax = (uu___134_6319.lax);
        lax_universes = (uu___134_6319.lax_universes);
        type_of = (uu___134_6319.type_of);
        universe_of = (uu___134_6319.universe_of);
        use_bv_sorts = (uu___134_6319.use_bv_sorts);
        qname_and_index = (uu___134_6319.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6337 =
        FStar_List.map
          (fun fpns  ->
             let uu____6348 =
               let uu____6349 =
                 let uu____6350 =
                   FStar_List.map
                     (fun uu____6355  ->
                        match uu____6355 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6350 in
               Prims.strcat uu____6349 "]" in
             Prims.strcat "[" uu____6348) pns in
      FStar_String.concat ";" uu____6337 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6364  -> ());
    push = (fun uu____6365  -> ());
    pop = (fun uu____6366  -> ());
    mark = (fun uu____6367  -> ());
    reset_mark = (fun uu____6368  -> ());
    commit_mark = (fun uu____6369  -> ());
    encode_modul = (fun uu____6370  -> fun uu____6371  -> ());
    encode_sig = (fun uu____6372  -> fun uu____6373  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6380  -> fun uu____6381  -> fun uu____6382  -> ());
    is_trivial = (fun uu____6386  -> fun uu____6387  -> false);
    finish = (fun uu____6388  -> ());
    refresh = (fun uu____6389  -> ())
  }