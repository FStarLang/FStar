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
      Prims.option;}
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
                                                               Prims.option))
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
  expected_typ: FStar_Syntax_Syntax.typ Prims.option;
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
  qname_and_index: (FStar_Ident.lident* Prims.int) Prims.option;
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
    (Prims.unit -> Prims.string) Prims.option ->
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
      | (NoDelta ,_)
        |(Eager_unfolding_only
          ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
         |(Unfold _,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          |(Unfold _,FStar_Syntax_Syntax.Visible_default ) -> true
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
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt Prims.option =
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
    let uu____1407 = FStar_Unionfind.fresh None in
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
      | ((formals,t),uu____1430) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1446 = FStar_Syntax_Subst.subst vs t in (us, uu____1446)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1451  ->
    match uu___100_1451 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1465  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1475 = inst_tscheme t in
      match uu____1475 with
      | (us,t1) ->
          let uu____1482 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1482)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1494  ->
          match uu____1494 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1508 =
                         let uu____1509 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1512 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1515 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1516 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1509 uu____1512 uu____1515 uu____1516 in
                       failwith uu____1508)
                    else ();
                    (let uu____1518 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     Prims.snd uu____1518))
               | uu____1522 ->
                   let uu____1523 =
                     let uu____1524 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1524 in
                   failwith uu____1523)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1528 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1532 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1536 -> false
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
             | ([],uu____1562) -> Maybe
             | (uu____1566,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1578 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                                   FStar_Syntax_Syntax.universes
                                                                   Prims.option))
        FStar_Util.either* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t in
      let found =
        if cur_mod <> No
        then
          let uu____1638 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1638 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1659  ->
                   match uu___101_1659 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1682 =
                           let uu____1692 =
                             let uu____1700 = inst_tscheme t in
                             FStar_Util.Inl uu____1700 in
                           (uu____1692, (FStar_Ident.range_of_lid l)) in
                         Some uu____1682
                       else None
                   | Binding_sig
                       (uu____1734,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1736);
                                     FStar_Syntax_Syntax.sigrng = uu____1737;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1738;
                                     FStar_Syntax_Syntax.sigmeta = uu____1739;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1748 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1748
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1775 ->
                             Some t
                         | uu____1779 -> cache t in
                       let uu____1780 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1780 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1820 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1820 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1864 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1906 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1906
         then
           let uu____1917 = find_in_sigtab env lid in
           match uu____1917 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1983) ->
          add_sigelts env ses
      | uu____1988 ->
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
            | uu____1997 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___102_2015  ->
           match uu___102_2015 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2028 -> None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
        FStar_Range.range) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2049,lb::[]),uu____2051,uu____2052) ->
          let uu____2061 =
            let uu____2066 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2072 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2066, uu____2072) in
          Some uu____2061
      | FStar_Syntax_Syntax.Sig_let ((uu____2079,lbs),uu____2081,uu____2082)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2102 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2109 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2109
                   then
                     let uu____2115 =
                       let uu____2120 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2126 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2120, uu____2126) in
                     Some uu____2115
                   else None)
      | uu____2138 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) Prims.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2157 =
          let uu____2162 =
            let uu____2165 =
              let uu____2166 =
                let uu____2169 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2169 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2166) in
            inst_tscheme uu____2165 in
          (uu____2162, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2157
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2183,uu____2184) ->
        let uu____2187 =
          let uu____2192 =
            let uu____2195 =
              let uu____2196 =
                let uu____2199 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2199 in
              (us, uu____2196) in
            inst_tscheme uu____2195 in
          (uu____2192, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2187
    | uu____2210 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2245 =
        match uu____2245 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2295,uvs,t,uu____2298,uu____2299,uu____2300);
                    FStar_Syntax_Syntax.sigrng = uu____2301;
                    FStar_Syntax_Syntax.sigquals = uu____2302;
                    FStar_Syntax_Syntax.sigmeta = uu____2303;_},None
                  )
                 ->
                 let uu____2313 =
                   let uu____2318 = inst_tscheme (uvs, t) in
                   (uu____2318, rng) in
                 Some uu____2313
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2330;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2332;_},None
                  )
                 ->
                 let uu____2340 =
                   let uu____2341 = in_cur_mod env l in uu____2341 = Yes in
                 if uu____2340
                 then
                   let uu____2347 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2347
                    then
                      let uu____2354 =
                        let uu____2359 = inst_tscheme (uvs, t) in
                        (uu____2359, rng) in
                      Some uu____2354
                    else None)
                 else
                   (let uu____2374 =
                      let uu____2379 = inst_tscheme (uvs, t) in
                      (uu____2379, rng) in
                    Some uu____2374)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2392,uu____2393);
                    FStar_Syntax_Syntax.sigrng = uu____2394;
                    FStar_Syntax_Syntax.sigquals = uu____2395;
                    FStar_Syntax_Syntax.sigmeta = uu____2396;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2415 =
                        let uu____2420 = inst_tscheme (uvs, k) in
                        (uu____2420, rng) in
                      Some uu____2415
                  | uu____2429 ->
                      let uu____2430 =
                        let uu____2435 =
                          let uu____2438 =
                            let uu____2439 =
                              let uu____2442 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2442 in
                            (uvs, uu____2439) in
                          inst_tscheme uu____2438 in
                        (uu____2435, rng) in
                      Some uu____2430)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2457,uu____2458);
                    FStar_Syntax_Syntax.sigrng = uu____2459;
                    FStar_Syntax_Syntax.sigquals = uu____2460;
                    FStar_Syntax_Syntax.sigmeta = uu____2461;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2481 =
                        let uu____2486 = inst_tscheme_with (uvs, k) us in
                        (uu____2486, rng) in
                      Some uu____2481
                  | uu____2495 ->
                      let uu____2496 =
                        let uu____2501 =
                          let uu____2504 =
                            let uu____2505 =
                              let uu____2508 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2508 in
                            (uvs, uu____2505) in
                          inst_tscheme_with uu____2504 us in
                        (uu____2501, rng) in
                      Some uu____2496)
             | FStar_Util.Inr se ->
                 let uu____2528 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2539;
                        FStar_Syntax_Syntax.sigrng = uu____2540;
                        FStar_Syntax_Syntax.sigquals = uu____2541;
                        FStar_Syntax_Syntax.sigmeta = uu____2542;_},None
                      ) -> lookup_type_of_let (Prims.fst se) lid
                   | uu____2551 -> effect_signature (Prims.fst se) in
                 FStar_All.pipe_right uu____2528
                   (FStar_Util.map_option
                      (fun uu____2574  ->
                         match uu____2574 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2591 =
        let uu____2597 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2597 mapper in
      match uu____2591 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2649 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2649.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2649.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2649.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2670 = lookup_qname env l in
      match uu____2670 with | None  -> false | Some uu____2690 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2718 = try_lookup_bv env bv in
      match uu____2718 with
      | None  ->
          let uu____2726 =
            let uu____2727 =
              let uu____2730 = variable_not_found bv in (uu____2730, bvr) in
            FStar_Errors.Error uu____2727 in
          Prims.raise uu____2726
      | Some (t,r) ->
          let uu____2737 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2738 = FStar_Range.set_use_range r bvr in
          (uu____2737, uu____2738)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2750 = try_lookup_lid_aux env l in
      match uu____2750 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2792 =
            let uu____2797 =
              let uu____2800 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2800) in
            (uu____2797, r1) in
          Some uu____2792
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2817 = try_lookup_lid env l in
      match uu____2817 with
      | None  ->
          let uu____2831 =
            let uu____2832 =
              let uu____2835 = name_not_found l in
              (uu____2835, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2832 in
          Prims.raise uu____2831
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2856  ->
              match uu___103_2856 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2858 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2869 = lookup_qname env lid in
      match uu____2869 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2884,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2887;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2889;_},None
            ),uu____2890)
          ->
          let uu____2914 =
            let uu____2920 =
              let uu____2923 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2923) in
            (uu____2920, q) in
          Some uu____2914
      | uu____2932 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2954 = lookup_qname env lid in
      match uu____2954 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2967,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2970;
              FStar_Syntax_Syntax.sigquals = uu____2971;
              FStar_Syntax_Syntax.sigmeta = uu____2972;_},None
            ),uu____2973)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2997 ->
          let uu____3008 =
            let uu____3009 =
              let uu____3012 = name_not_found lid in
              (uu____3012, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3009 in
          Prims.raise uu____3008
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3023 = lookup_qname env lid in
      match uu____3023 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3036,uvs,t,uu____3039,uu____3040,uu____3041);
              FStar_Syntax_Syntax.sigrng = uu____3042;
              FStar_Syntax_Syntax.sigquals = uu____3043;
              FStar_Syntax_Syntax.sigmeta = uu____3044;_},None
            ),uu____3045)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3071 ->
          let uu____3082 =
            let uu____3083 =
              let uu____3086 = name_not_found lid in
              (uu____3086, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3083 in
          Prims.raise uu____3082
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3098 = lookup_qname env lid in
      match uu____3098 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3112,uu____3113,uu____3114,uu____3115,uu____3116,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3118;
              FStar_Syntax_Syntax.sigquals = uu____3119;
              FStar_Syntax_Syntax.sigmeta = uu____3120;_},uu____3121),uu____3122)
          -> (true, dcs)
      | uu____3152 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3170 = lookup_qname env lid in
      match uu____3170 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3181,uu____3182,uu____3183,l,uu____3185,uu____3186);
              FStar_Syntax_Syntax.sigrng = uu____3187;
              FStar_Syntax_Syntax.sigquals = uu____3188;
              FStar_Syntax_Syntax.sigmeta = uu____3189;_},uu____3190),uu____3191)
          -> l
      | uu____3218 ->
          let uu____3229 =
            let uu____3230 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3230 in
          failwith uu____3229
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names* FStar_Syntax_Syntax.term)
          Prims.option
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
        let uu____3254 = lookup_qname env lid in
        match uu____3254 with
        | Some (FStar_Util.Inr (se,None ),uu____3269) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3295,lbs),uu____3297,uu____3298) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3313 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3313
                      then
                        let uu____3318 =
                          let uu____3322 =
                            let uu____3323 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3323 in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3322) in
                        Some uu____3318
                      else None)
             | uu____3332 -> None)
        | uu____3335 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3356 = lookup_qname env ftv in
      match uu____3356 with
      | Some (FStar_Util.Inr (se,None ),uu____3369) ->
          let uu____3392 = effect_signature se in
          (match uu____3392 with
           | None  -> None
           | Some ((uu____3403,t),r) ->
               let uu____3412 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3412)
      | uu____3413 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3430 = try_lookup_effect_lid env ftv in
      match uu____3430 with
      | None  ->
          let uu____3432 =
            let uu____3433 =
              let uu____3436 = name_not_found ftv in
              (uu____3436, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3433 in
          Prims.raise uu____3432
      | Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp) Prims.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3450 = lookup_qname env lid0 in
        match uu____3450 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3468);
                FStar_Syntax_Syntax.sigrng = uu____3469;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3471;_},None
              ),uu____3472)
            ->
            let lid1 =
              let uu____3499 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3499 in
            let uu____3500 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3502  ->
                      match uu___104_3502 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3503 -> false)) in
            if uu____3500
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
                     (let uu____3519 =
                        let uu____3520 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3521 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3520 uu____3521 in
                      failwith uu____3519) in
               match (binders, univs1) with
               | ([],uu____3527) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3536,uu____3537::uu____3538::uu____3539) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3542 =
                     let uu____3543 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3544 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3543 uu____3544 in
                   failwith uu____3542
               | uu____3550 ->
                   let uu____3553 =
                     let uu____3556 =
                       let uu____3557 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3557) in
                     inst_tscheme_with uu____3556 insts in
                   (match uu____3553 with
                    | (uu____3565,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3568 =
                          let uu____3569 = FStar_Syntax_Subst.compress t1 in
                          uu____3569.FStar_Syntax_Syntax.n in
                        (match uu____3568 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3599 -> failwith "Impossible")))
        | uu____3603 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3629 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3629 with
        | None  -> None
        | Some (uu____3636,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3641 = find1 l2 in
            (match uu____3641 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3646 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3646 with
        | Some l1 -> l1
        | None  ->
            let uu____3649 = find1 l in
            (match uu____3649 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3661 = lookup_qname env l1 in
      match uu____3661 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3673;
              FStar_Syntax_Syntax.sigrng = uu____3674;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3676;_},uu____3677),uu____3678)
          -> q
      | uu____3703 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3726 =
          let uu____3727 =
            let uu____3728 = FStar_Util.string_of_int i in
            let uu____3729 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3728 uu____3729 in
          failwith uu____3727 in
        let uu____3730 = lookup_datacon env lid in
        match uu____3730 with
        | (uu____3733,t) ->
            let uu____3735 =
              let uu____3736 = FStar_Syntax_Subst.compress t in
              uu____3736.FStar_Syntax_Syntax.n in
            (match uu____3735 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3740) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3761 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i in
                    FStar_All.pipe_right uu____3761 Prims.fst)
             | uu____3766 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3773 = lookup_qname env l in
      match uu____3773 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3784,uu____3785,uu____3786);
              FStar_Syntax_Syntax.sigrng = uu____3787;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3789;_},uu____3790),uu____3791)
          ->
          FStar_Util.for_some
            (fun uu___105_3816  ->
               match uu___105_3816 with
               | FStar_Syntax_Syntax.Projector uu____3817 -> true
               | uu____3820 -> false) quals
      | uu____3821 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3838 = lookup_qname env lid in
      match uu____3838 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3849,uu____3850,uu____3851,uu____3852,uu____3853,uu____3854);
              FStar_Syntax_Syntax.sigrng = uu____3855;
              FStar_Syntax_Syntax.sigquals = uu____3856;
              FStar_Syntax_Syntax.sigmeta = uu____3857;_},uu____3858),uu____3859)
          -> true
      | uu____3886 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3903 = lookup_qname env lid in
      match uu____3903 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3914,uu____3915,uu____3916,uu____3917,uu____3918,uu____3919);
              FStar_Syntax_Syntax.sigrng = uu____3920;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3922;_},uu____3923),uu____3924)
          ->
          FStar_Util.for_some
            (fun uu___106_3953  ->
               match uu___106_3953 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3956 -> false) quals
      | uu____3957 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3974 = lookup_qname env lid in
      match uu____3974 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3985,uu____3986,uu____3987);
              FStar_Syntax_Syntax.sigrng = uu____3988;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3990;_},uu____3991),uu____3992)
          ->
          FStar_Util.for_some
            (fun uu___107_4021  ->
               match uu___107_4021 with
               | FStar_Syntax_Syntax.Action uu____4022 -> true
               | uu____4023 -> false) quals
      | uu____4024 -> false
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
      let uu____4043 =
        let uu____4044 = FStar_Syntax_Util.un_uinst head1 in
        uu____4044.FStar_Syntax_Syntax.n in
      match uu____4043 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4048 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____4086 -> Some false
        | FStar_Util.Inr (se,uu____4095) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4104 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4108 -> Some true
             | uu____4117 -> Some false) in
      let uu____4118 =
        let uu____4120 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4120 mapper in
      match uu____4118 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4147 = lookup_qname env lid in
      match uu____4147 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4158,uu____4159,tps,uu____4161,uu____4162,uu____4163);
              FStar_Syntax_Syntax.sigrng = uu____4164;
              FStar_Syntax_Syntax.sigquals = uu____4165;
              FStar_Syntax_Syntax.sigmeta = uu____4166;_},uu____4167),uu____4168)
          -> FStar_List.length tps
      | uu____4200 ->
          let uu____4211 =
            let uu____4212 =
              let uu____4215 = name_not_found lid in
              (uu____4215, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4212 in
          Prims.raise uu____4211
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl* FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4237  ->
              match uu____4237 with
              | (d,uu____4242) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4251 = effect_decl_opt env l in
      match uu____4251 with
      | None  ->
          let uu____4259 =
            let uu____4260 =
              let uu____4263 = name_not_found l in
              (uu____4263, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4260 in
          Prims.raise uu____4259
      | Some md -> Prims.fst md
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
            (let uu____4306 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4330  ->
                       match uu____4330 with
                       | (m1,m2,uu____4338,uu____4339,uu____4340) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4306 with
             | None  ->
                 let uu____4349 =
                   let uu____4350 =
                     let uu____4353 =
                       let uu____4354 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4355 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4354
                         uu____4355 in
                     (uu____4353, (env.range)) in
                   FStar_Errors.Error uu____4350 in
                 Prims.raise uu____4349
             | Some (uu____4359,uu____4360,m3,j1,j2) -> (m3, j1, j2))
let monad_leq:
  env -> FStar_Ident.lident -> FStar_Ident.lident -> edge Prims.option =
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
  let uu____4407 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4419  ->
            match uu____4419 with
            | (d,uu____4423) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4407 with
  | None  ->
      let uu____4430 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4430
  | Some (md,_q) ->
      let uu____4439 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4439 with
       | (uu____4446,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4454)::(wp,uu____4456)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4478 -> failwith "Impossible"))
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
                 let uu____4514 = get_range env in
                 let uu____4515 =
                   let uu____4518 =
                     let uu____4519 =
                       let uu____4529 =
                         let uu____4531 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4531] in
                       (null_wp, uu____4529) in
                     FStar_Syntax_Syntax.Tm_app uu____4519 in
                   FStar_Syntax_Syntax.mk uu____4518 in
                 uu____4515 None uu____4514 in
               let uu____4541 =
                 let uu____4542 =
                   let uu____4548 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4548] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4542;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4541)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4557 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4557.order);
              joins = (uu___118_4557.joins)
            } in
          let uu___119_4562 = env in
          {
            solver = (uu___119_4562.solver);
            range = (uu___119_4562.range);
            curmodule = (uu___119_4562.curmodule);
            gamma = (uu___119_4562.gamma);
            gamma_cache = (uu___119_4562.gamma_cache);
            modules = (uu___119_4562.modules);
            expected_typ = (uu___119_4562.expected_typ);
            sigtab = (uu___119_4562.sigtab);
            is_pattern = (uu___119_4562.is_pattern);
            instantiate_imp = (uu___119_4562.instantiate_imp);
            effects;
            generalize = (uu___119_4562.generalize);
            letrecs = (uu___119_4562.letrecs);
            top_level = (uu___119_4562.top_level);
            check_uvars = (uu___119_4562.check_uvars);
            use_eq = (uu___119_4562.use_eq);
            is_iface = (uu___119_4562.is_iface);
            admit = (uu___119_4562.admit);
            lax = (uu___119_4562.lax);
            lax_universes = (uu___119_4562.lax_universes);
            type_of = (uu___119_4562.type_of);
            universe_of = (uu___119_4562.universe_of);
            use_bv_sorts = (uu___119_4562.use_bv_sorts);
            qname_and_index = (uu___119_4562.qname_and_index);
            proof_ns = (uu___119_4562.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4579 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4579 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4658 = (e1.mlift).mlift_wp t wp in
                              let uu____4659 = l1 t wp e in
                              l2 t uu____4658 uu____4659))
                | uu____4660 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4695 = inst_tscheme lift_t in
            match uu____4695 with
            | (uu____4700,lift_t1) ->
                let uu____4702 =
                  let uu____4705 =
                    let uu____4706 =
                      let uu____4716 =
                        let uu____4718 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4719 =
                          let uu____4721 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4721] in
                        uu____4718 :: uu____4719 in
                      (lift_t1, uu____4716) in
                    FStar_Syntax_Syntax.Tm_app uu____4706 in
                  FStar_Syntax_Syntax.mk uu____4705 in
                uu____4702 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4766 = inst_tscheme lift_t in
            match uu____4766 with
            | (uu____4771,lift_t1) ->
                let uu____4773 =
                  let uu____4776 =
                    let uu____4777 =
                      let uu____4787 =
                        let uu____4789 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4790 =
                          let uu____4792 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4793 =
                            let uu____4795 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4795] in
                          uu____4792 :: uu____4793 in
                        uu____4789 :: uu____4790 in
                      (lift_t1, uu____4787) in
                    FStar_Syntax_Syntax.Tm_app uu____4777 in
                  FStar_Syntax_Syntax.mk uu____4776 in
                uu____4773 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4836 =
                let uu____4837 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4837
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4836 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4841 =
              let uu____4842 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4842 in
            let uu____4843 =
              let uu____4844 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4859 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4859) in
              FStar_Util.dflt "none" uu____4844 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4841
              uu____4843 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4872  ->
                    match uu____4872 with
                    | (e,uu____4877) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4890 =
            match uu____4890 with
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
              let uu____4915 =
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
                                    (let uu____4927 =
                                       let uu____4932 =
                                         find_edge order1 (i, k) in
                                       let uu____4934 =
                                         find_edge order1 (k, j) in
                                       (uu____4932, uu____4934) in
                                     match uu____4927 with
                                     | (Some e1,Some e2) ->
                                         let uu____4943 = compose_edges e1 e2 in
                                         [uu____4943]
                                     | uu____4944 -> []))))) in
              FStar_List.append order1 uu____4915 in
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
                   let uu____4959 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4960 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4960
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4959
                   then
                     let uu____4963 =
                       let uu____4964 =
                         let uu____4967 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4968 = get_range env in
                         (uu____4967, uu____4968) in
                       FStar_Errors.Error uu____4964 in
                     Prims.raise uu____4963
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
                                            let uu____5031 =
                                              let uu____5036 =
                                                find_edge order2 (i, k) in
                                              let uu____5038 =
                                                find_edge order2 (j, k) in
                                              (uu____5036, uu____5038) in
                                            match uu____5031 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5061,uu____5062)
                                                     ->
                                                     let uu____5066 =
                                                       let uu____5069 =
                                                         let uu____5070 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5070 in
                                                       let uu____5072 =
                                                         let uu____5073 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5073 in
                                                       (uu____5069,
                                                         uu____5072) in
                                                     (match uu____5066 with
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
                                            | uu____5092 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5131 = env.effects in
              { decls = (uu___120_5131.decls); order = order2; joins } in
            let uu___121_5132 = env in
            {
              solver = (uu___121_5132.solver);
              range = (uu___121_5132.range);
              curmodule = (uu___121_5132.curmodule);
              gamma = (uu___121_5132.gamma);
              gamma_cache = (uu___121_5132.gamma_cache);
              modules = (uu___121_5132.modules);
              expected_typ = (uu___121_5132.expected_typ);
              sigtab = (uu___121_5132.sigtab);
              is_pattern = (uu___121_5132.is_pattern);
              instantiate_imp = (uu___121_5132.instantiate_imp);
              effects;
              generalize = (uu___121_5132.generalize);
              letrecs = (uu___121_5132.letrecs);
              top_level = (uu___121_5132.top_level);
              check_uvars = (uu___121_5132.check_uvars);
              use_eq = (uu___121_5132.use_eq);
              is_iface = (uu___121_5132.is_iface);
              admit = (uu___121_5132.admit);
              lax = (uu___121_5132.lax);
              lax_universes = (uu___121_5132.lax_universes);
              type_of = (uu___121_5132.type_of);
              universe_of = (uu___121_5132.universe_of);
              use_bv_sorts = (uu___121_5132.use_bv_sorts);
              qname_and_index = (uu___121_5132.qname_and_index);
              proof_ns = (uu___121_5132.proof_ns)
            }))
      | uu____5133 -> env
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
        | uu____5155 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5163 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5163 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5173 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5173 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5190 =
                     let uu____5191 =
                       let uu____5194 =
                         let uu____5195 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5201 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5209 =
                           let uu____5210 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5210 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5195 uu____5201 uu____5209 in
                       (uu____5194, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5191 in
                   Prims.raise uu____5190)
                else ();
                (let inst1 =
                   let uu____5214 =
                     let uu____5220 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5220 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5227  ->
                        fun uu____5228  ->
                          match (uu____5227, uu____5228) with
                          | ((x,uu____5242),(t,uu____5244)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5214 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5259 =
                     let uu___122_5260 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5260.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5260.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5260.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5260.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5259
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5290 =
    let uu____5295 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5295 in
  match uu____5290 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5311 =
        only_reifiable &&
          (let uu____5312 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5312) in
      if uu____5311
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5325 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5327 =
               let uu____5336 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5336) in
             (match uu____5327 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5370 =
                    let uu____5373 = get_range env in
                    let uu____5374 =
                      let uu____5377 =
                        let uu____5378 =
                          let uu____5388 =
                            let uu____5390 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5390; wp] in
                          (repr, uu____5388) in
                        FStar_Syntax_Syntax.Tm_app uu____5378 in
                      FStar_Syntax_Syntax.mk uu____5377 in
                    uu____5374 None uu____5373 in
                  Some uu____5370))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax Prims.option
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
          let uu____5434 =
            let uu____5435 =
              let uu____5438 =
                let uu____5439 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5439 in
              let uu____5440 = get_range env in (uu____5438, uu____5440) in
            FStar_Errors.Error uu____5435 in
          Prims.raise uu____5434 in
        let uu____5441 = effect_repr_aux true env c u_c in
        match uu____5441 with
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
        | FStar_Util.Inr (eff_name,uu____5473) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5486 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5493 =
        let uu____5494 = FStar_Syntax_Subst.compress t in
        uu____5494.FStar_Syntax_Syntax.n in
      match uu____5493 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5497,c) ->
          is_reifiable_comp env c
      | uu____5509 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5534 = push1 x rest1 in local :: uu____5534 in
      let uu___123_5536 = env in
      let uu____5537 = push1 s env.gamma in
      {
        solver = (uu___123_5536.solver);
        range = (uu___123_5536.range);
        curmodule = (uu___123_5536.curmodule);
        gamma = uu____5537;
        gamma_cache = (uu___123_5536.gamma_cache);
        modules = (uu___123_5536.modules);
        expected_typ = (uu___123_5536.expected_typ);
        sigtab = (uu___123_5536.sigtab);
        is_pattern = (uu___123_5536.is_pattern);
        instantiate_imp = (uu___123_5536.instantiate_imp);
        effects = (uu___123_5536.effects);
        generalize = (uu___123_5536.generalize);
        letrecs = (uu___123_5536.letrecs);
        top_level = (uu___123_5536.top_level);
        check_uvars = (uu___123_5536.check_uvars);
        use_eq = (uu___123_5536.use_eq);
        is_iface = (uu___123_5536.is_iface);
        admit = (uu___123_5536.admit);
        lax = (uu___123_5536.lax);
        lax_universes = (uu___123_5536.lax_universes);
        type_of = (uu___123_5536.type_of);
        universe_of = (uu___123_5536.universe_of);
        use_bv_sorts = (uu___123_5536.use_bv_sorts);
        qname_and_index = (uu___123_5536.qname_and_index);
        proof_ns = (uu___123_5536.proof_ns)
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
      let uu___124_5564 = env in
      {
        solver = (uu___124_5564.solver);
        range = (uu___124_5564.range);
        curmodule = (uu___124_5564.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5564.gamma_cache);
        modules = (uu___124_5564.modules);
        expected_typ = (uu___124_5564.expected_typ);
        sigtab = (uu___124_5564.sigtab);
        is_pattern = (uu___124_5564.is_pattern);
        instantiate_imp = (uu___124_5564.instantiate_imp);
        effects = (uu___124_5564.effects);
        generalize = (uu___124_5564.generalize);
        letrecs = (uu___124_5564.letrecs);
        top_level = (uu___124_5564.top_level);
        check_uvars = (uu___124_5564.check_uvars);
        use_eq = (uu___124_5564.use_eq);
        is_iface = (uu___124_5564.is_iface);
        admit = (uu___124_5564.admit);
        lax = (uu___124_5564.lax);
        lax_universes = (uu___124_5564.lax_universes);
        type_of = (uu___124_5564.type_of);
        universe_of = (uu___124_5564.universe_of);
        use_bv_sorts = (uu___124_5564.use_bv_sorts);
        qname_and_index = (uu___124_5564.qname_and_index);
        proof_ns = (uu___124_5564.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) Prims.option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5585 = env in
             {
               solver = (uu___125_5585.solver);
               range = (uu___125_5585.range);
               curmodule = (uu___125_5585.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5585.gamma_cache);
               modules = (uu___125_5585.modules);
               expected_typ = (uu___125_5585.expected_typ);
               sigtab = (uu___125_5585.sigtab);
               is_pattern = (uu___125_5585.is_pattern);
               instantiate_imp = (uu___125_5585.instantiate_imp);
               effects = (uu___125_5585.effects);
               generalize = (uu___125_5585.generalize);
               letrecs = (uu___125_5585.letrecs);
               top_level = (uu___125_5585.top_level);
               check_uvars = (uu___125_5585.check_uvars);
               use_eq = (uu___125_5585.use_eq);
               is_iface = (uu___125_5585.is_iface);
               admit = (uu___125_5585.admit);
               lax = (uu___125_5585.lax);
               lax_universes = (uu___125_5585.lax_universes);
               type_of = (uu___125_5585.type_of);
               universe_of = (uu___125_5585.universe_of);
               use_bv_sorts = (uu___125_5585.use_bv_sorts);
               qname_and_index = (uu___125_5585.qname_and_index);
               proof_ns = (uu___125_5585.proof_ns)
             }))
    | uu____5586 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5599  ->
             match uu____5599 with | (x,uu____5603) -> push_bv env1 x) env bs
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
            let uu___126_5623 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5623.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5623.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (Prims.snd t)
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
      (let uu___127_5653 = env in
       {
         solver = (uu___127_5653.solver);
         range = (uu___127_5653.range);
         curmodule = (uu___127_5653.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5653.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5653.sigtab);
         is_pattern = (uu___127_5653.is_pattern);
         instantiate_imp = (uu___127_5653.instantiate_imp);
         effects = (uu___127_5653.effects);
         generalize = (uu___127_5653.generalize);
         letrecs = (uu___127_5653.letrecs);
         top_level = (uu___127_5653.top_level);
         check_uvars = (uu___127_5653.check_uvars);
         use_eq = (uu___127_5653.use_eq);
         is_iface = (uu___127_5653.is_iface);
         admit = (uu___127_5653.admit);
         lax = (uu___127_5653.lax);
         lax_universes = (uu___127_5653.lax_universes);
         type_of = (uu___127_5653.type_of);
         universe_of = (uu___127_5653.universe_of);
         use_bv_sorts = (uu___127_5653.use_bv_sorts);
         qname_and_index = (uu___127_5653.qname_and_index);
         proof_ns = (uu___127_5653.proof_ns)
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
        let uu____5677 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5677 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5693 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5693)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5703 = env in
      {
        solver = (uu___128_5703.solver);
        range = (uu___128_5703.range);
        curmodule = (uu___128_5703.curmodule);
        gamma = (uu___128_5703.gamma);
        gamma_cache = (uu___128_5703.gamma_cache);
        modules = (uu___128_5703.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5703.sigtab);
        is_pattern = (uu___128_5703.is_pattern);
        instantiate_imp = (uu___128_5703.instantiate_imp);
        effects = (uu___128_5703.effects);
        generalize = (uu___128_5703.generalize);
        letrecs = (uu___128_5703.letrecs);
        top_level = (uu___128_5703.top_level);
        check_uvars = (uu___128_5703.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5703.is_iface);
        admit = (uu___128_5703.admit);
        lax = (uu___128_5703.lax);
        lax_universes = (uu___128_5703.lax_universes);
        type_of = (uu___128_5703.type_of);
        universe_of = (uu___128_5703.universe_of);
        use_bv_sorts = (uu___128_5703.use_bv_sorts);
        qname_and_index = (uu___128_5703.qname_and_index);
        proof_ns = (uu___128_5703.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ Prims.option) =
  fun env_  ->
    let uu____5719 = expected_typ env_ in
    ((let uu___129_5722 = env_ in
      {
        solver = (uu___129_5722.solver);
        range = (uu___129_5722.range);
        curmodule = (uu___129_5722.curmodule);
        gamma = (uu___129_5722.gamma);
        gamma_cache = (uu___129_5722.gamma_cache);
        modules = (uu___129_5722.modules);
        expected_typ = None;
        sigtab = (uu___129_5722.sigtab);
        is_pattern = (uu___129_5722.is_pattern);
        instantiate_imp = (uu___129_5722.instantiate_imp);
        effects = (uu___129_5722.effects);
        generalize = (uu___129_5722.generalize);
        letrecs = (uu___129_5722.letrecs);
        top_level = (uu___129_5722.top_level);
        check_uvars = (uu___129_5722.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5722.is_iface);
        admit = (uu___129_5722.admit);
        lax = (uu___129_5722.lax);
        lax_universes = (uu___129_5722.lax_universes);
        type_of = (uu___129_5722.type_of);
        universe_of = (uu___129_5722.universe_of);
        use_bv_sorts = (uu___129_5722.use_bv_sorts);
        qname_and_index = (uu___129_5722.qname_and_index);
        proof_ns = (uu___129_5722.proof_ns)
      }), uu____5719)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5733 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5737  ->
                    match uu___108_5737 with
                    | Binding_sig (uu____5739,se) -> [se]
                    | uu____5743 -> [])) in
          FStar_All.pipe_right uu____5733 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5748 = env in
       {
         solver = (uu___130_5748.solver);
         range = (uu___130_5748.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5748.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5748.expected_typ);
         sigtab = (uu___130_5748.sigtab);
         is_pattern = (uu___130_5748.is_pattern);
         instantiate_imp = (uu___130_5748.instantiate_imp);
         effects = (uu___130_5748.effects);
         generalize = (uu___130_5748.generalize);
         letrecs = (uu___130_5748.letrecs);
         top_level = (uu___130_5748.top_level);
         check_uvars = (uu___130_5748.check_uvars);
         use_eq = (uu___130_5748.use_eq);
         is_iface = (uu___130_5748.is_iface);
         admit = (uu___130_5748.admit);
         lax = (uu___130_5748.lax);
         lax_universes = (uu___130_5748.lax_universes);
         type_of = (uu___130_5748.type_of);
         universe_of = (uu___130_5748.universe_of);
         use_bv_sorts = (uu___130_5748.use_bv_sorts);
         qname_and_index = (uu___130_5748.qname_and_index);
         proof_ns = (uu___130_5748.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5798)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5813 =
            let uu____5817 = FStar_Syntax_Free.uvars t in ext out uu____5817 in
          aux uu____5813 tl1
      | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> out in
    aux no_uvs1 env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst _)::tl1|(Binding_univ _)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5873 =
            let uu____5875 = FStar_Syntax_Free.univs t in ext out uu____5875 in
          aux uu____5873 tl1
      | (Binding_sig uu____5877)::uu____5878 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5915)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5925 = FStar_Util.set_add uname out in aux uu____5925 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5939 =
            let uu____5941 = FStar_Syntax_Free.univnames t in
            ext out uu____5941 in
          aux uu____5939 tl1
      | (Binding_sig uu____5943)::uu____5944 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_5960  ->
            match uu___109_5960 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5972 =
      let uu____5974 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____5974
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____5972 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____5990 =
      let uu____5991 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_5995  ->
                match uu___110_5995 with
                | Binding_var x ->
                    let uu____5997 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____5997
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6000) ->
                    let uu____6001 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6001
                | Binding_sig (ls,uu____6003) ->
                    let uu____6006 =
                      let uu____6007 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6007
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6006
                | Binding_sig_inst (ls,uu____6013,uu____6014) ->
                    let uu____6017 =
                      let uu____6018 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6018
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6017)) in
      FStar_All.pipe_right uu____5991 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____5990 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6030 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6030
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6047  ->
                 fun uu____6048  ->
                   match (uu____6047, uu____6048) with
                   | ((b1,uu____6058),(b2,uu____6060)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6103  ->
             match uu___111_6103 with
             | Binding_sig (lids,uu____6107) -> FStar_List.append lids keys
             | uu____6110 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6112  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6137) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6149,uu____6150) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6174 = list_prefix p path1 in
            if uu____6174 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6184 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6184
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___131_6204 = e in
            {
              solver = (uu___131_6204.solver);
              range = (uu___131_6204.range);
              curmodule = (uu___131_6204.curmodule);
              gamma = (uu___131_6204.gamma);
              gamma_cache = (uu___131_6204.gamma_cache);
              modules = (uu___131_6204.modules);
              expected_typ = (uu___131_6204.expected_typ);
              sigtab = (uu___131_6204.sigtab);
              is_pattern = (uu___131_6204.is_pattern);
              instantiate_imp = (uu___131_6204.instantiate_imp);
              effects = (uu___131_6204.effects);
              generalize = (uu___131_6204.generalize);
              letrecs = (uu___131_6204.letrecs);
              top_level = (uu___131_6204.top_level);
              check_uvars = (uu___131_6204.check_uvars);
              use_eq = (uu___131_6204.use_eq);
              is_iface = (uu___131_6204.is_iface);
              admit = (uu___131_6204.admit);
              lax = (uu___131_6204.lax);
              lax_universes = (uu___131_6204.lax_universes);
              type_of = (uu___131_6204.type_of);
              universe_of = (uu___131_6204.universe_of);
              use_bv_sorts = (uu___131_6204.use_bv_sorts);
              qname_and_index = (uu___131_6204.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___132_6223 = e in
    {
      solver = (uu___132_6223.solver);
      range = (uu___132_6223.range);
      curmodule = (uu___132_6223.curmodule);
      gamma = (uu___132_6223.gamma);
      gamma_cache = (uu___132_6223.gamma_cache);
      modules = (uu___132_6223.modules);
      expected_typ = (uu___132_6223.expected_typ);
      sigtab = (uu___132_6223.sigtab);
      is_pattern = (uu___132_6223.is_pattern);
      instantiate_imp = (uu___132_6223.instantiate_imp);
      effects = (uu___132_6223.effects);
      generalize = (uu___132_6223.generalize);
      letrecs = (uu___132_6223.letrecs);
      top_level = (uu___132_6223.top_level);
      check_uvars = (uu___132_6223.check_uvars);
      use_eq = (uu___132_6223.use_eq);
      is_iface = (uu___132_6223.is_iface);
      admit = (uu___132_6223.admit);
      lax = (uu___132_6223.lax);
      lax_universes = (uu___132_6223.lax_universes);
      type_of = (uu___132_6223.type_of);
      universe_of = (uu___132_6223.universe_of);
      use_bv_sorts = (uu___132_6223.use_bv_sorts);
      qname_and_index = (uu___132_6223.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6232::rest ->
        let uu___133_6235 = e in
        {
          solver = (uu___133_6235.solver);
          range = (uu___133_6235.range);
          curmodule = (uu___133_6235.curmodule);
          gamma = (uu___133_6235.gamma);
          gamma_cache = (uu___133_6235.gamma_cache);
          modules = (uu___133_6235.modules);
          expected_typ = (uu___133_6235.expected_typ);
          sigtab = (uu___133_6235.sigtab);
          is_pattern = (uu___133_6235.is_pattern);
          instantiate_imp = (uu___133_6235.instantiate_imp);
          effects = (uu___133_6235.effects);
          generalize = (uu___133_6235.generalize);
          letrecs = (uu___133_6235.letrecs);
          top_level = (uu___133_6235.top_level);
          check_uvars = (uu___133_6235.check_uvars);
          use_eq = (uu___133_6235.use_eq);
          is_iface = (uu___133_6235.is_iface);
          admit = (uu___133_6235.admit);
          lax = (uu___133_6235.lax);
          lax_universes = (uu___133_6235.lax_universes);
          type_of = (uu___133_6235.type_of);
          universe_of = (uu___133_6235.universe_of);
          use_bv_sorts = (uu___133_6235.use_bv_sorts);
          qname_and_index = (uu___133_6235.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___134_6245 = e in
      {
        solver = (uu___134_6245.solver);
        range = (uu___134_6245.range);
        curmodule = (uu___134_6245.curmodule);
        gamma = (uu___134_6245.gamma);
        gamma_cache = (uu___134_6245.gamma_cache);
        modules = (uu___134_6245.modules);
        expected_typ = (uu___134_6245.expected_typ);
        sigtab = (uu___134_6245.sigtab);
        is_pattern = (uu___134_6245.is_pattern);
        instantiate_imp = (uu___134_6245.instantiate_imp);
        effects = (uu___134_6245.effects);
        generalize = (uu___134_6245.generalize);
        letrecs = (uu___134_6245.letrecs);
        top_level = (uu___134_6245.top_level);
        check_uvars = (uu___134_6245.check_uvars);
        use_eq = (uu___134_6245.use_eq);
        is_iface = (uu___134_6245.is_iface);
        admit = (uu___134_6245.admit);
        lax = (uu___134_6245.lax);
        lax_universes = (uu___134_6245.lax_universes);
        type_of = (uu___134_6245.type_of);
        universe_of = (uu___134_6245.universe_of);
        use_bv_sorts = (uu___134_6245.use_bv_sorts);
        qname_and_index = (uu___134_6245.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6263 =
        FStar_List.map
          (fun fpns  ->
             let uu____6274 =
               let uu____6275 =
                 let uu____6276 =
                   FStar_List.map
                     (fun uu____6281  ->
                        match uu____6281 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6276 in
               Prims.strcat uu____6275 "]" in
             Prims.strcat "[" uu____6274) pns in
      FStar_String.concat ";" uu____6263 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6290  -> ());
    push = (fun uu____6291  -> ());
    pop = (fun uu____6292  -> ());
    mark = (fun uu____6293  -> ());
    reset_mark = (fun uu____6294  -> ());
    commit_mark = (fun uu____6295  -> ());
    encode_modul = (fun uu____6296  -> fun uu____6297  -> ());
    encode_sig = (fun uu____6298  -> fun uu____6299  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6306  -> fun uu____6307  -> fun uu____6308  -> ());
    is_trivial = (fun uu____6312  -> fun uu____6313  -> false);
    finish = (fun uu____6314  -> ());
    refresh = (fun uu____6315  -> ())
  }