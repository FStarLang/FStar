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
      | uu____860 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____870 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____878 =
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
          let uu____917 = new_gamma_cache () in
          let uu____919 = new_sigtab () in
          let uu____921 =
            let uu____922 = FStar_Options.using_facts_from () in
            match uu____922 with
            | Some ns ->
                let uu____928 =
                  let uu____933 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____933 [([], false)] in
                [uu____928]
            | None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____917;
            modules = [];
            expected_typ = None;
            sigtab = uu____919;
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
            proof_ns = uu____921
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1011  ->
    let uu____1012 = FStar_ST.read query_indices in
    match uu____1012 with
    | [] -> failwith "Empty query indices!"
    | uu____1026 ->
        let uu____1031 =
          let uu____1036 =
            let uu____1040 = FStar_ST.read query_indices in
            FStar_List.hd uu____1040 in
          let uu____1054 = FStar_ST.read query_indices in uu____1036 ::
            uu____1054 in
        FStar_ST.write query_indices uu____1031
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1076  ->
    let uu____1077 = FStar_ST.read query_indices in
    match uu____1077 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1113  ->
    match uu____1113 with
    | (l,n1) ->
        let uu____1118 = FStar_ST.read query_indices in
        (match uu____1118 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1152 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1162  ->
    let uu____1163 = FStar_ST.read query_indices in FStar_List.hd uu____1163
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1179  ->
    let uu____1180 = FStar_ST.read query_indices in
    match uu____1180 with
    | hd1::uu____1192::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1219 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1233 =
       let uu____1235 = FStar_ST.read stack in env :: uu____1235 in
     FStar_ST.write stack uu____1233);
    (let uu___115_1243 = env in
     let uu____1244 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1246 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___115_1243.solver);
       range = (uu___115_1243.range);
       curmodule = (uu___115_1243.curmodule);
       gamma = (uu___115_1243.gamma);
       gamma_cache = uu____1244;
       modules = (uu___115_1243.modules);
       expected_typ = (uu___115_1243.expected_typ);
       sigtab = uu____1246;
       is_pattern = (uu___115_1243.is_pattern);
       instantiate_imp = (uu___115_1243.instantiate_imp);
       effects = (uu___115_1243.effects);
       generalize = (uu___115_1243.generalize);
       letrecs = (uu___115_1243.letrecs);
       top_level = (uu___115_1243.top_level);
       check_uvars = (uu___115_1243.check_uvars);
       use_eq = (uu___115_1243.use_eq);
       is_iface = (uu___115_1243.is_iface);
       admit = (uu___115_1243.admit);
       lax = (uu___115_1243.lax);
       lax_universes = (uu___115_1243.lax_universes);
       type_of = (uu___115_1243.type_of);
       universe_of = (uu___115_1243.universe_of);
       use_bv_sorts = (uu___115_1243.use_bv_sorts);
       qname_and_index = (uu___115_1243.qname_and_index);
       proof_ns = (uu___115_1243.proof_ns)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1250  ->
    let uu____1251 = FStar_ST.read stack in
    match uu____1251 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1263 -> failwith "Impossible: Too many pops"
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
    (let uu____1295 = pop_stack () in ());
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
        let uu____1314 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1326  ->
                  match uu____1326 with
                  | (m,uu____1330) -> FStar_Ident.lid_equals l m)) in
        (match uu____1314 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_1335 = env in
               {
                 solver = (uu___116_1335.solver);
                 range = (uu___116_1335.range);
                 curmodule = (uu___116_1335.curmodule);
                 gamma = (uu___116_1335.gamma);
                 gamma_cache = (uu___116_1335.gamma_cache);
                 modules = (uu___116_1335.modules);
                 expected_typ = (uu___116_1335.expected_typ);
                 sigtab = (uu___116_1335.sigtab);
                 is_pattern = (uu___116_1335.is_pattern);
                 instantiate_imp = (uu___116_1335.instantiate_imp);
                 effects = (uu___116_1335.effects);
                 generalize = (uu___116_1335.generalize);
                 letrecs = (uu___116_1335.letrecs);
                 top_level = (uu___116_1335.top_level);
                 check_uvars = (uu___116_1335.check_uvars);
                 use_eq = (uu___116_1335.use_eq);
                 is_iface = (uu___116_1335.is_iface);
                 admit = (uu___116_1335.admit);
                 lax = (uu___116_1335.lax);
                 lax_universes = (uu___116_1335.lax_universes);
                 type_of = (uu___116_1335.type_of);
                 universe_of = (uu___116_1335.universe_of);
                 use_bv_sorts = (uu___116_1335.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___116_1335.proof_ns)
               }))
         | Some (uu____1338,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___117_1344 = env in
               {
                 solver = (uu___117_1344.solver);
                 range = (uu___117_1344.range);
                 curmodule = (uu___117_1344.curmodule);
                 gamma = (uu___117_1344.gamma);
                 gamma_cache = (uu___117_1344.gamma_cache);
                 modules = (uu___117_1344.modules);
                 expected_typ = (uu___117_1344.expected_typ);
                 sigtab = (uu___117_1344.sigtab);
                 is_pattern = (uu___117_1344.is_pattern);
                 instantiate_imp = (uu___117_1344.instantiate_imp);
                 effects = (uu___117_1344.effects);
                 generalize = (uu___117_1344.generalize);
                 letrecs = (uu___117_1344.letrecs);
                 top_level = (uu___117_1344.top_level);
                 check_uvars = (uu___117_1344.check_uvars);
                 use_eq = (uu___117_1344.use_eq);
                 is_iface = (uu___117_1344.is_iface);
                 admit = (uu___117_1344.admit);
                 lax = (uu___117_1344.lax);
                 lax_universes = (uu___117_1344.lax_universes);
                 type_of = (uu___117_1344.type_of);
                 universe_of = (uu___117_1344.universe_of);
                 use_bv_sorts = (uu___117_1344.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___117_1344.proof_ns)
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
        (let uu___118_1360 = e in
         {
           solver = (uu___118_1360.solver);
           range = r;
           curmodule = (uu___118_1360.curmodule);
           gamma = (uu___118_1360.gamma);
           gamma_cache = (uu___118_1360.gamma_cache);
           modules = (uu___118_1360.modules);
           expected_typ = (uu___118_1360.expected_typ);
           sigtab = (uu___118_1360.sigtab);
           is_pattern = (uu___118_1360.is_pattern);
           instantiate_imp = (uu___118_1360.instantiate_imp);
           effects = (uu___118_1360.effects);
           generalize = (uu___118_1360.generalize);
           letrecs = (uu___118_1360.letrecs);
           top_level = (uu___118_1360.top_level);
           check_uvars = (uu___118_1360.check_uvars);
           use_eq = (uu___118_1360.use_eq);
           is_iface = (uu___118_1360.is_iface);
           admit = (uu___118_1360.admit);
           lax = (uu___118_1360.lax);
           lax_universes = (uu___118_1360.lax_universes);
           type_of = (uu___118_1360.type_of);
           universe_of = (uu___118_1360.universe_of);
           use_bv_sorts = (uu___118_1360.use_bv_sorts);
           qname_and_index = (uu___118_1360.qname_and_index);
           proof_ns = (uu___118_1360.proof_ns)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___119_1377 = env in
      {
        solver = (uu___119_1377.solver);
        range = (uu___119_1377.range);
        curmodule = lid;
        gamma = (uu___119_1377.gamma);
        gamma_cache = (uu___119_1377.gamma_cache);
        modules = (uu___119_1377.modules);
        expected_typ = (uu___119_1377.expected_typ);
        sigtab = (uu___119_1377.sigtab);
        is_pattern = (uu___119_1377.is_pattern);
        instantiate_imp = (uu___119_1377.instantiate_imp);
        effects = (uu___119_1377.effects);
        generalize = (uu___119_1377.generalize);
        letrecs = (uu___119_1377.letrecs);
        top_level = (uu___119_1377.top_level);
        check_uvars = (uu___119_1377.check_uvars);
        use_eq = (uu___119_1377.use_eq);
        is_iface = (uu___119_1377.is_iface);
        admit = (uu___119_1377.admit);
        lax = (uu___119_1377.lax);
        lax_universes = (uu___119_1377.lax_universes);
        type_of = (uu___119_1377.type_of);
        universe_of = (uu___119_1377.universe_of);
        use_bv_sorts = (uu___119_1377.use_bv_sorts);
        qname_and_index = (uu___119_1377.qname_and_index);
        proof_ns = (uu___119_1377.proof_ns)
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
    let uu____1399 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1399
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1402  ->
    let uu____1403 = FStar_Unionfind.fresh None in
    FStar_Syntax_Syntax.U_unif uu____1403
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1426) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1442 = FStar_Syntax_Subst.subst vs t in (us, uu____1442)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___103_1447  ->
    match uu___103_1447 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1461  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1471 = inst_tscheme t in
      match uu____1471 with
      | (us,t1) ->
          let uu____1478 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1478)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1490  ->
          match uu____1490 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1504 =
                         let uu____1505 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1508 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1511 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1512 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1505 uu____1508 uu____1511 uu____1512 in
                       failwith uu____1504)
                    else ();
                    (let uu____1514 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     Prims.snd uu____1514))
               | uu____1518 ->
                   let uu____1519 =
                     let uu____1520 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1520 in
                   failwith uu____1519)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1524 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1528 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1532 -> false
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
             | ([],uu____1558) -> Maybe
             | (uu____1562,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1574 -> No in
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
          let uu____1634 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1634 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___104_1655  ->
                   match uu___104_1655 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1678 =
                           let uu____1688 =
                             let uu____1696 = inst_tscheme t in
                             FStar_Util.Inl uu____1696 in
                           (uu____1688, (FStar_Ident.range_of_lid l)) in
                         Some uu____1678
                       else None
                   | Binding_sig
                       (uu____1730,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1732);
                                     FStar_Syntax_Syntax.sigrng = uu____1733;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1734;
                                     FStar_Syntax_Syntax.sigmeta = uu____1735;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1744 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1744
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1771 ->
                             Some t
                         | uu____1775 -> cache t in
                       let uu____1776 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1776 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1816 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1816 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1860 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1902 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1902
         then
           let uu____1913 = find_in_sigtab env lid in
           match uu____1913 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1979) ->
          add_sigelts env ses
      | uu____1984 ->
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
            | uu____1993 -> ()))
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
        (fun uu___105_2011  ->
           match uu___105_2011 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2024 -> None)
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
          ((uu____2045,lb::[]),uu____2047,uu____2048) ->
          let uu____2057 =
            let uu____2062 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2068 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2062, uu____2068) in
          Some uu____2057
      | FStar_Syntax_Syntax.Sig_let ((uu____2075,lbs),uu____2077,uu____2078)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2098 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2105 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2105
                   then
                     let uu____2111 =
                       let uu____2116 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2122 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2116, uu____2122) in
                     Some uu____2111
                   else None)
      | uu____2134 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) Prims.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2153 =
          let uu____2158 =
            let uu____2161 =
              let uu____2162 =
                let uu____2165 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2165 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2162) in
            inst_tscheme uu____2161 in
          (uu____2158, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2153
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2179,uu____2180) ->
        let uu____2183 =
          let uu____2188 =
            let uu____2191 =
              let uu____2192 =
                let uu____2195 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2195 in
              (us, uu____2192) in
            inst_tscheme uu____2191 in
          (uu____2188, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2183
    | uu____2206 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2241 =
        match uu____2241 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2291,uvs,t,uu____2294,uu____2295,uu____2296);
                    FStar_Syntax_Syntax.sigrng = uu____2297;
                    FStar_Syntax_Syntax.sigquals = uu____2298;
                    FStar_Syntax_Syntax.sigmeta = uu____2299;_},None
                  )
                 ->
                 let uu____2309 =
                   let uu____2314 = inst_tscheme (uvs, t) in
                   (uu____2314, rng) in
                 Some uu____2309
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2326;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2328;_},None
                  )
                 ->
                 let uu____2336 =
                   let uu____2337 = in_cur_mod env l in uu____2337 = Yes in
                 if uu____2336
                 then
                   let uu____2343 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2343
                    then
                      let uu____2350 =
                        let uu____2355 = inst_tscheme (uvs, t) in
                        (uu____2355, rng) in
                      Some uu____2350
                    else None)
                 else
                   (let uu____2370 =
                      let uu____2375 = inst_tscheme (uvs, t) in
                      (uu____2375, rng) in
                    Some uu____2370)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2388,uu____2389);
                    FStar_Syntax_Syntax.sigrng = uu____2390;
                    FStar_Syntax_Syntax.sigquals = uu____2391;
                    FStar_Syntax_Syntax.sigmeta = uu____2392;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2411 =
                        let uu____2416 = inst_tscheme (uvs, k) in
                        (uu____2416, rng) in
                      Some uu____2411
                  | uu____2425 ->
                      let uu____2426 =
                        let uu____2431 =
                          let uu____2434 =
                            let uu____2435 =
                              let uu____2438 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2438 in
                            (uvs, uu____2435) in
                          inst_tscheme uu____2434 in
                        (uu____2431, rng) in
                      Some uu____2426)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2453,uu____2454);
                    FStar_Syntax_Syntax.sigrng = uu____2455;
                    FStar_Syntax_Syntax.sigquals = uu____2456;
                    FStar_Syntax_Syntax.sigmeta = uu____2457;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2477 =
                        let uu____2482 = inst_tscheme_with (uvs, k) us in
                        (uu____2482, rng) in
                      Some uu____2477
                  | uu____2491 ->
                      let uu____2492 =
                        let uu____2497 =
                          let uu____2500 =
                            let uu____2501 =
                              let uu____2504 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2504 in
                            (uvs, uu____2501) in
                          inst_tscheme_with uu____2500 us in
                        (uu____2497, rng) in
                      Some uu____2492)
             | FStar_Util.Inr se ->
                 let uu____2524 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2535;
                        FStar_Syntax_Syntax.sigrng = uu____2536;
                        FStar_Syntax_Syntax.sigquals = uu____2537;
                        FStar_Syntax_Syntax.sigmeta = uu____2538;_},None
                      ) -> lookup_type_of_let (Prims.fst se) lid
                   | uu____2547 -> effect_signature (Prims.fst se) in
                 FStar_All.pipe_right uu____2524
                   (FStar_Util.map_option
                      (fun uu____2570  ->
                         match uu____2570 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2587 =
        let uu____2593 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2593 mapper in
      match uu____2587 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___120_2645 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_2645.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___120_2645.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_2645.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2666 = lookup_qname env l in
      match uu____2666 with | None  -> false | Some uu____2686 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2714 = try_lookup_bv env bv in
      match uu____2714 with
      | None  ->
          let uu____2722 =
            let uu____2723 =
              let uu____2726 = variable_not_found bv in (uu____2726, bvr) in
            FStar_Errors.Error uu____2723 in
          Prims.raise uu____2722
      | Some (t,r) ->
          let uu____2733 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2734 = FStar_Range.set_use_range r bvr in
          (uu____2733, uu____2734)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2746 = try_lookup_lid_aux env l in
      match uu____2746 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2788 =
            let uu____2793 =
              let uu____2796 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2796) in
            (uu____2793, r1) in
          Some uu____2788
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2813 = try_lookup_lid env l in
      match uu____2813 with
      | None  ->
          let uu____2827 =
            let uu____2828 =
              let uu____2831 = name_not_found l in
              (uu____2831, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2828 in
          Prims.raise uu____2827
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_2852  ->
              match uu___106_2852 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2854 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2865 = lookup_qname env lid in
      match uu____2865 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2880,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2883;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2885;_},None
            ),uu____2886)
          ->
          let uu____2910 =
            let uu____2916 =
              let uu____2919 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2919) in
            (uu____2916, q) in
          Some uu____2910
      | uu____2928 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2950 = lookup_qname env lid in
      match uu____2950 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2963,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2966;
              FStar_Syntax_Syntax.sigquals = uu____2967;
              FStar_Syntax_Syntax.sigmeta = uu____2968;_},None
            ),uu____2969)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2993 ->
          let uu____3004 =
            let uu____3005 =
              let uu____3008 = name_not_found lid in
              (uu____3008, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3005 in
          Prims.raise uu____3004
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3019 = lookup_qname env lid in
      match uu____3019 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3032,uvs,t,uu____3035,uu____3036,uu____3037);
              FStar_Syntax_Syntax.sigrng = uu____3038;
              FStar_Syntax_Syntax.sigquals = uu____3039;
              FStar_Syntax_Syntax.sigmeta = uu____3040;_},None
            ),uu____3041)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3067 ->
          let uu____3078 =
            let uu____3079 =
              let uu____3082 = name_not_found lid in
              (uu____3082, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3079 in
          Prims.raise uu____3078
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3094 = lookup_qname env lid in
      match uu____3094 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3108,uu____3109,uu____3110,uu____3111,uu____3112,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3114;
              FStar_Syntax_Syntax.sigquals = uu____3115;
              FStar_Syntax_Syntax.sigmeta = uu____3116;_},uu____3117),uu____3118)
          -> (true, dcs)
      | uu____3148 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3166 = lookup_qname env lid in
      match uu____3166 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3177,uu____3178,uu____3179,l,uu____3181,uu____3182);
              FStar_Syntax_Syntax.sigrng = uu____3183;
              FStar_Syntax_Syntax.sigquals = uu____3184;
              FStar_Syntax_Syntax.sigmeta = uu____3185;_},uu____3186),uu____3187)
          -> l
      | uu____3214 ->
          let uu____3225 =
            let uu____3226 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3226 in
          failwith uu____3225
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
        let uu____3250 = lookup_qname env lid in
        match uu____3250 with
        | Some (FStar_Util.Inr (se,None ),uu____3265) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3291,lbs),uu____3293,uu____3294) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3309 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3309
                      then
                        let uu____3314 =
                          let uu____3318 =
                            let uu____3319 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3319 in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3318) in
                        Some uu____3314
                      else None)
             | uu____3328 -> None)
        | uu____3331 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3352 = lookup_qname env ftv in
      match uu____3352 with
      | Some (FStar_Util.Inr (se,None ),uu____3365) ->
          let uu____3388 = effect_signature se in
          (match uu____3388 with
           | None  -> None
           | Some ((uu____3399,t),r) ->
               let uu____3408 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3408)
      | uu____3409 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3426 = try_lookup_effect_lid env ftv in
      match uu____3426 with
      | None  ->
          let uu____3428 =
            let uu____3429 =
              let uu____3432 = name_not_found ftv in
              (uu____3432, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3429 in
          Prims.raise uu____3428
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
        let uu____3446 = lookup_qname env lid0 in
        match uu____3446 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3464);
                FStar_Syntax_Syntax.sigrng = uu____3465;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3467;_},None
              ),uu____3468)
            ->
            let lid1 =
              let uu____3495 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3495 in
            let uu____3496 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_3498  ->
                      match uu___107_3498 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3499 -> false)) in
            if uu____3496
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
                     (let uu____3515 =
                        let uu____3516 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3517 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3516 uu____3517 in
                      failwith uu____3515) in
               match (binders, univs1) with
               | ([],uu____3523) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3532,uu____3533::uu____3534::uu____3535) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3538 =
                     let uu____3539 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3540 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3539 uu____3540 in
                   failwith uu____3538
               | uu____3546 ->
                   let uu____3549 =
                     let uu____3552 =
                       let uu____3553 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3553) in
                     inst_tscheme_with uu____3552 insts in
                   (match uu____3549 with
                    | (uu____3561,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3564 =
                          let uu____3565 = FStar_Syntax_Subst.compress t1 in
                          uu____3565.FStar_Syntax_Syntax.n in
                        (match uu____3564 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3595 -> failwith "Impossible")))
        | uu____3599 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3625 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3625 with
        | None  -> None
        | Some (uu____3632,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3637 = find1 l2 in
            (match uu____3637 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3642 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3642 with
        | Some l1 -> l1
        | None  ->
            let uu____3645 = find1 l in
            (match uu____3645 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3657 = lookup_qname env l1 in
      match uu____3657 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3669;
              FStar_Syntax_Syntax.sigrng = uu____3670;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3672;_},uu____3673),uu____3674)
          -> q
      | uu____3699 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3722 =
          let uu____3723 =
            let uu____3724 = FStar_Util.string_of_int i in
            let uu____3725 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3724 uu____3725 in
          failwith uu____3723 in
        let uu____3726 = lookup_datacon env lid in
        match uu____3726 with
        | (uu____3729,t) ->
            let uu____3731 =
              let uu____3732 = FStar_Syntax_Subst.compress t in
              uu____3732.FStar_Syntax_Syntax.n in
            (match uu____3731 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3736) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3757 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i in
                    FStar_All.pipe_right uu____3757 Prims.fst)
             | uu____3762 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3769 = lookup_qname env l in
      match uu____3769 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3780,uu____3781,uu____3782);
              FStar_Syntax_Syntax.sigrng = uu____3783;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3785;_},uu____3786),uu____3787)
          ->
          FStar_Util.for_some
            (fun uu___108_3812  ->
               match uu___108_3812 with
               | FStar_Syntax_Syntax.Projector uu____3813 -> true
               | uu____3816 -> false) quals
      | uu____3817 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3834 = lookup_qname env lid in
      match uu____3834 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3845,uu____3846,uu____3847,uu____3848,uu____3849,uu____3850);
              FStar_Syntax_Syntax.sigrng = uu____3851;
              FStar_Syntax_Syntax.sigquals = uu____3852;
              FStar_Syntax_Syntax.sigmeta = uu____3853;_},uu____3854),uu____3855)
          -> true
      | uu____3882 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3899 = lookup_qname env lid in
      match uu____3899 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3910,uu____3911,uu____3912,uu____3913,uu____3914,uu____3915);
              FStar_Syntax_Syntax.sigrng = uu____3916;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3918;_},uu____3919),uu____3920)
          ->
          FStar_Util.for_some
            (fun uu___109_3949  ->
               match uu___109_3949 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3952 -> false) quals
      | uu____3953 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3970 = lookup_qname env lid in
      match uu____3970 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3981,uu____3982,uu____3983);
              FStar_Syntax_Syntax.sigrng = uu____3984;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3986;_},uu____3987),uu____3988)
          ->
          FStar_Util.for_some
            (fun uu___110_4017  ->
               match uu___110_4017 with
               | FStar_Syntax_Syntax.Action uu____4018 -> true
               | uu____4019 -> false) quals
      | uu____4020 -> false
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
      let uu____4039 =
        let uu____4040 = FStar_Syntax_Util.un_uinst head1 in
        uu____4040.FStar_Syntax_Syntax.n in
      match uu____4039 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4044 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____4082 -> Some false
        | FStar_Util.Inr (se,uu____4091) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4100 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4104 -> Some true
             | uu____4113 -> Some false) in
      let uu____4114 =
        let uu____4116 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4116 mapper in
      match uu____4114 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4143 = lookup_qname env lid in
      match uu____4143 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4154,uu____4155,tps,uu____4157,uu____4158,uu____4159);
              FStar_Syntax_Syntax.sigrng = uu____4160;
              FStar_Syntax_Syntax.sigquals = uu____4161;
              FStar_Syntax_Syntax.sigmeta = uu____4162;_},uu____4163),uu____4164)
          -> FStar_List.length tps
      | uu____4196 ->
          let uu____4207 =
            let uu____4208 =
              let uu____4211 = name_not_found lid in
              (uu____4211, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4208 in
          Prims.raise uu____4207
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
           (fun uu____4233  ->
              match uu____4233 with
              | (d,uu____4238) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4247 = effect_decl_opt env l in
      match uu____4247 with
      | None  ->
          let uu____4255 =
            let uu____4256 =
              let uu____4259 = name_not_found l in
              (uu____4259, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4256 in
          Prims.raise uu____4255
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
            (let uu____4302 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4326  ->
                       match uu____4326 with
                       | (m1,m2,uu____4334,uu____4335,uu____4336) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4302 with
             | None  ->
                 let uu____4345 =
                   let uu____4346 =
                     let uu____4349 =
                       let uu____4350 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4351 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4350
                         uu____4351 in
                     (uu____4349, (env.range)) in
                   FStar_Errors.Error uu____4346 in
                 Prims.raise uu____4345
             | Some (uu____4355,uu____4356,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4403 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4415  ->
            match uu____4415 with
            | (d,uu____4419) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4403 with
  | None  ->
      let uu____4426 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4426
  | Some (md,_q) ->
      let uu____4435 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4435 with
       | (uu____4442,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4450)::(wp,uu____4452)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4474 -> failwith "Impossible"))
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
                 let uu____4510 = get_range env in
                 let uu____4511 =
                   let uu____4514 =
                     let uu____4515 =
                       let uu____4525 =
                         let uu____4527 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4527] in
                       (null_wp, uu____4525) in
                     FStar_Syntax_Syntax.Tm_app uu____4515 in
                   FStar_Syntax_Syntax.mk uu____4514 in
                 uu____4511 None uu____4510 in
               let uu____4537 =
                 let uu____4538 =
                   let uu____4544 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4544] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4538;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4537)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_4553 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_4553.order);
              joins = (uu___121_4553.joins)
            } in
          let uu___122_4558 = env in
          {
            solver = (uu___122_4558.solver);
            range = (uu___122_4558.range);
            curmodule = (uu___122_4558.curmodule);
            gamma = (uu___122_4558.gamma);
            gamma_cache = (uu___122_4558.gamma_cache);
            modules = (uu___122_4558.modules);
            expected_typ = (uu___122_4558.expected_typ);
            sigtab = (uu___122_4558.sigtab);
            is_pattern = (uu___122_4558.is_pattern);
            instantiate_imp = (uu___122_4558.instantiate_imp);
            effects;
            generalize = (uu___122_4558.generalize);
            letrecs = (uu___122_4558.letrecs);
            top_level = (uu___122_4558.top_level);
            check_uvars = (uu___122_4558.check_uvars);
            use_eq = (uu___122_4558.use_eq);
            is_iface = (uu___122_4558.is_iface);
            admit = (uu___122_4558.admit);
            lax = (uu___122_4558.lax);
            lax_universes = (uu___122_4558.lax_universes);
            type_of = (uu___122_4558.type_of);
            universe_of = (uu___122_4558.universe_of);
            use_bv_sorts = (uu___122_4558.use_bv_sorts);
            qname_and_index = (uu___122_4558.qname_and_index);
            proof_ns = (uu___122_4558.proof_ns)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4575 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4575 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4654 = (e1.mlift).mlift_wp t wp in
                              let uu____4655 = l1 t wp e in
                              l2 t uu____4654 uu____4655))
                | uu____4656 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4691 = inst_tscheme lift_t in
            match uu____4691 with
            | (uu____4696,lift_t1) ->
                let uu____4698 =
                  let uu____4701 =
                    let uu____4702 =
                      let uu____4712 =
                        let uu____4714 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4715 =
                          let uu____4717 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4717] in
                        uu____4714 :: uu____4715 in
                      (lift_t1, uu____4712) in
                    FStar_Syntax_Syntax.Tm_app uu____4702 in
                  FStar_Syntax_Syntax.mk uu____4701 in
                uu____4698 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4762 = inst_tscheme lift_t in
            match uu____4762 with
            | (uu____4767,lift_t1) ->
                let uu____4769 =
                  let uu____4772 =
                    let uu____4773 =
                      let uu____4783 =
                        let uu____4785 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4786 =
                          let uu____4788 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4789 =
                            let uu____4791 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4791] in
                          uu____4788 :: uu____4789 in
                        uu____4785 :: uu____4786 in
                      (lift_t1, uu____4783) in
                    FStar_Syntax_Syntax.Tm_app uu____4773 in
                  FStar_Syntax_Syntax.mk uu____4772 in
                uu____4769 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4832 =
                let uu____4833 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4833
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4832 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4837 =
              let uu____4838 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4838 in
            let uu____4839 =
              let uu____4840 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4855 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4855) in
              FStar_Util.dflt "none" uu____4840 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4837
              uu____4839 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4868  ->
                    match uu____4868 with
                    | (e,uu____4873) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4886 =
            match uu____4886 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_28  -> Some _0_28)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____4911 =
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
                                    (let uu____4923 =
                                       let uu____4928 =
                                         find_edge order1 (i, k) in
                                       let uu____4930 =
                                         find_edge order1 (k, j) in
                                       (uu____4928, uu____4930) in
                                     match uu____4923 with
                                     | (Some e1,Some e2) ->
                                         let uu____4939 = compose_edges e1 e2 in
                                         [uu____4939]
                                     | uu____4940 -> []))))) in
              FStar_List.append order1 uu____4911 in
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
                   let uu____4955 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4956 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4956
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4955
                   then
                     let uu____4959 =
                       let uu____4960 =
                         let uu____4963 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4964 = get_range env in
                         (uu____4963, uu____4964) in
                       FStar_Errors.Error uu____4960 in
                     Prims.raise uu____4959
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
                                            let uu____5027 =
                                              let uu____5032 =
                                                find_edge order2 (i, k) in
                                              let uu____5034 =
                                                find_edge order2 (j, k) in
                                              (uu____5032, uu____5034) in
                                            match uu____5027 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5057,uu____5058)
                                                     ->
                                                     let uu____5062 =
                                                       let uu____5065 =
                                                         let uu____5066 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5066 in
                                                       let uu____5068 =
                                                         let uu____5069 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5069 in
                                                       (uu____5065,
                                                         uu____5068) in
                                                     (match uu____5062 with
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
                                            | uu____5088 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_5127 = env.effects in
              { decls = (uu___123_5127.decls); order = order2; joins } in
            let uu___124_5128 = env in
            {
              solver = (uu___124_5128.solver);
              range = (uu___124_5128.range);
              curmodule = (uu___124_5128.curmodule);
              gamma = (uu___124_5128.gamma);
              gamma_cache = (uu___124_5128.gamma_cache);
              modules = (uu___124_5128.modules);
              expected_typ = (uu___124_5128.expected_typ);
              sigtab = (uu___124_5128.sigtab);
              is_pattern = (uu___124_5128.is_pattern);
              instantiate_imp = (uu___124_5128.instantiate_imp);
              effects;
              generalize = (uu___124_5128.generalize);
              letrecs = (uu___124_5128.letrecs);
              top_level = (uu___124_5128.top_level);
              check_uvars = (uu___124_5128.check_uvars);
              use_eq = (uu___124_5128.use_eq);
              is_iface = (uu___124_5128.is_iface);
              admit = (uu___124_5128.admit);
              lax = (uu___124_5128.lax);
              lax_universes = (uu___124_5128.lax_universes);
              type_of = (uu___124_5128.type_of);
              universe_of = (uu___124_5128.universe_of);
              use_bv_sorts = (uu___124_5128.use_bv_sorts);
              qname_and_index = (uu___124_5128.qname_and_index);
              proof_ns = (uu___124_5128.proof_ns)
            }))
      | uu____5129 -> env
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
        | uu____5151 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5159 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5159 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5169 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5169 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5186 =
                     let uu____5187 =
                       let uu____5190 =
                         let uu____5191 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5197 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5205 =
                           let uu____5206 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5206 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5191 uu____5197 uu____5205 in
                       (uu____5190, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5187 in
                   Prims.raise uu____5186)
                else ();
                (let inst1 =
                   let uu____5210 =
                     let uu____5216 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5216 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5223  ->
                        fun uu____5224  ->
                          match (uu____5223, uu____5224) with
                          | ((x,uu____5238),(t,uu____5240)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5210 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5255 =
                     let uu___125_5256 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_5256.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_5256.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_5256.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_5256.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5255
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5286 =
    let uu____5291 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5291 in
  match uu____5286 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5307 =
        only_reifiable &&
          (let uu____5308 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5308) in
      if uu____5307
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5321 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5323 =
               let uu____5332 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5332) in
             (match uu____5323 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5366 =
                    let uu____5369 = get_range env in
                    let uu____5370 =
                      let uu____5373 =
                        let uu____5374 =
                          let uu____5384 =
                            let uu____5386 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5386; wp] in
                          (repr, uu____5384) in
                        FStar_Syntax_Syntax.Tm_app uu____5374 in
                      FStar_Syntax_Syntax.mk uu____5373 in
                    uu____5370 None uu____5369 in
                  Some uu____5366))
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
          let uu____5430 =
            let uu____5431 =
              let uu____5434 =
                let uu____5435 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5435 in
              let uu____5436 = get_range env in (uu____5434, uu____5436) in
            FStar_Errors.Error uu____5431 in
          Prims.raise uu____5430 in
        let uu____5437 = effect_repr_aux true env c u_c in
        match uu____5437 with
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
        | FStar_Util.Inr (eff_name,uu____5469) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5482 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5489 =
        let uu____5490 = FStar_Syntax_Subst.compress t in
        uu____5490.FStar_Syntax_Syntax.n in
      match uu____5489 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5493,c) ->
          is_reifiable_comp env c
      | uu____5505 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5530 = push1 x rest1 in local :: uu____5530 in
      let uu___126_5532 = env in
      let uu____5533 = push1 s env.gamma in
      {
        solver = (uu___126_5532.solver);
        range = (uu___126_5532.range);
        curmodule = (uu___126_5532.curmodule);
        gamma = uu____5533;
        gamma_cache = (uu___126_5532.gamma_cache);
        modules = (uu___126_5532.modules);
        expected_typ = (uu___126_5532.expected_typ);
        sigtab = (uu___126_5532.sigtab);
        is_pattern = (uu___126_5532.is_pattern);
        instantiate_imp = (uu___126_5532.instantiate_imp);
        effects = (uu___126_5532.effects);
        generalize = (uu___126_5532.generalize);
        letrecs = (uu___126_5532.letrecs);
        top_level = (uu___126_5532.top_level);
        check_uvars = (uu___126_5532.check_uvars);
        use_eq = (uu___126_5532.use_eq);
        is_iface = (uu___126_5532.is_iface);
        admit = (uu___126_5532.admit);
        lax = (uu___126_5532.lax);
        lax_universes = (uu___126_5532.lax_universes);
        type_of = (uu___126_5532.type_of);
        universe_of = (uu___126_5532.universe_of);
        use_bv_sorts = (uu___126_5532.use_bv_sorts);
        qname_and_index = (uu___126_5532.qname_and_index);
        proof_ns = (uu___126_5532.proof_ns)
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
      let uu___127_5560 = env in
      {
        solver = (uu___127_5560.solver);
        range = (uu___127_5560.range);
        curmodule = (uu___127_5560.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_5560.gamma_cache);
        modules = (uu___127_5560.modules);
        expected_typ = (uu___127_5560.expected_typ);
        sigtab = (uu___127_5560.sigtab);
        is_pattern = (uu___127_5560.is_pattern);
        instantiate_imp = (uu___127_5560.instantiate_imp);
        effects = (uu___127_5560.effects);
        generalize = (uu___127_5560.generalize);
        letrecs = (uu___127_5560.letrecs);
        top_level = (uu___127_5560.top_level);
        check_uvars = (uu___127_5560.check_uvars);
        use_eq = (uu___127_5560.use_eq);
        is_iface = (uu___127_5560.is_iface);
        admit = (uu___127_5560.admit);
        lax = (uu___127_5560.lax);
        lax_universes = (uu___127_5560.lax_universes);
        type_of = (uu___127_5560.type_of);
        universe_of = (uu___127_5560.universe_of);
        use_bv_sorts = (uu___127_5560.use_bv_sorts);
        qname_and_index = (uu___127_5560.qname_and_index);
        proof_ns = (uu___127_5560.proof_ns)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) Prims.option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___128_5581 = env in
             {
               solver = (uu___128_5581.solver);
               range = (uu___128_5581.range);
               curmodule = (uu___128_5581.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_5581.gamma_cache);
               modules = (uu___128_5581.modules);
               expected_typ = (uu___128_5581.expected_typ);
               sigtab = (uu___128_5581.sigtab);
               is_pattern = (uu___128_5581.is_pattern);
               instantiate_imp = (uu___128_5581.instantiate_imp);
               effects = (uu___128_5581.effects);
               generalize = (uu___128_5581.generalize);
               letrecs = (uu___128_5581.letrecs);
               top_level = (uu___128_5581.top_level);
               check_uvars = (uu___128_5581.check_uvars);
               use_eq = (uu___128_5581.use_eq);
               is_iface = (uu___128_5581.is_iface);
               admit = (uu___128_5581.admit);
               lax = (uu___128_5581.lax);
               lax_universes = (uu___128_5581.lax_universes);
               type_of = (uu___128_5581.type_of);
               universe_of = (uu___128_5581.universe_of);
               use_bv_sorts = (uu___128_5581.use_bv_sorts);
               qname_and_index = (uu___128_5581.qname_and_index);
               proof_ns = (uu___128_5581.proof_ns)
             }))
    | uu____5582 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5595  ->
             match uu____5595 with | (x,uu____5599) -> push_bv env1 x) env bs
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
            let uu___129_5619 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_5619.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_5619.FStar_Syntax_Syntax.index);
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
      (let uu___130_5649 = env in
       {
         solver = (uu___130_5649.solver);
         range = (uu___130_5649.range);
         curmodule = (uu___130_5649.curmodule);
         gamma = [];
         gamma_cache = (uu___130_5649.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___130_5649.sigtab);
         is_pattern = (uu___130_5649.is_pattern);
         instantiate_imp = (uu___130_5649.instantiate_imp);
         effects = (uu___130_5649.effects);
         generalize = (uu___130_5649.generalize);
         letrecs = (uu___130_5649.letrecs);
         top_level = (uu___130_5649.top_level);
         check_uvars = (uu___130_5649.check_uvars);
         use_eq = (uu___130_5649.use_eq);
         is_iface = (uu___130_5649.is_iface);
         admit = (uu___130_5649.admit);
         lax = (uu___130_5649.lax);
         lax_universes = (uu___130_5649.lax_universes);
         type_of = (uu___130_5649.type_of);
         universe_of = (uu___130_5649.universe_of);
         use_bv_sorts = (uu___130_5649.use_bv_sorts);
         qname_and_index = (uu___130_5649.qname_and_index);
         proof_ns = (uu___130_5649.proof_ns)
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
        let uu____5673 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5673 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5689 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5689)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_5699 = env in
      {
        solver = (uu___131_5699.solver);
        range = (uu___131_5699.range);
        curmodule = (uu___131_5699.curmodule);
        gamma = (uu___131_5699.gamma);
        gamma_cache = (uu___131_5699.gamma_cache);
        modules = (uu___131_5699.modules);
        expected_typ = (Some t);
        sigtab = (uu___131_5699.sigtab);
        is_pattern = (uu___131_5699.is_pattern);
        instantiate_imp = (uu___131_5699.instantiate_imp);
        effects = (uu___131_5699.effects);
        generalize = (uu___131_5699.generalize);
        letrecs = (uu___131_5699.letrecs);
        top_level = (uu___131_5699.top_level);
        check_uvars = (uu___131_5699.check_uvars);
        use_eq = false;
        is_iface = (uu___131_5699.is_iface);
        admit = (uu___131_5699.admit);
        lax = (uu___131_5699.lax);
        lax_universes = (uu___131_5699.lax_universes);
        type_of = (uu___131_5699.type_of);
        universe_of = (uu___131_5699.universe_of);
        use_bv_sorts = (uu___131_5699.use_bv_sorts);
        qname_and_index = (uu___131_5699.qname_and_index);
        proof_ns = (uu___131_5699.proof_ns)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ Prims.option) =
  fun env_  ->
    let uu____5715 = expected_typ env_ in
    ((let uu___132_5718 = env_ in
      {
        solver = (uu___132_5718.solver);
        range = (uu___132_5718.range);
        curmodule = (uu___132_5718.curmodule);
        gamma = (uu___132_5718.gamma);
        gamma_cache = (uu___132_5718.gamma_cache);
        modules = (uu___132_5718.modules);
        expected_typ = None;
        sigtab = (uu___132_5718.sigtab);
        is_pattern = (uu___132_5718.is_pattern);
        instantiate_imp = (uu___132_5718.instantiate_imp);
        effects = (uu___132_5718.effects);
        generalize = (uu___132_5718.generalize);
        letrecs = (uu___132_5718.letrecs);
        top_level = (uu___132_5718.top_level);
        check_uvars = (uu___132_5718.check_uvars);
        use_eq = false;
        is_iface = (uu___132_5718.is_iface);
        admit = (uu___132_5718.admit);
        lax = (uu___132_5718.lax);
        lax_universes = (uu___132_5718.lax_universes);
        type_of = (uu___132_5718.type_of);
        universe_of = (uu___132_5718.universe_of);
        use_bv_sorts = (uu___132_5718.use_bv_sorts);
        qname_and_index = (uu___132_5718.qname_and_index);
        proof_ns = (uu___132_5718.proof_ns)
      }), uu____5715)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5729 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_5733  ->
                    match uu___111_5733 with
                    | Binding_sig (uu____5735,se) -> [se]
                    | uu____5739 -> [])) in
          FStar_All.pipe_right uu____5729 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_5744 = env in
       {
         solver = (uu___133_5744.solver);
         range = (uu___133_5744.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_5744.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_5744.expected_typ);
         sigtab = (uu___133_5744.sigtab);
         is_pattern = (uu___133_5744.is_pattern);
         instantiate_imp = (uu___133_5744.instantiate_imp);
         effects = (uu___133_5744.effects);
         generalize = (uu___133_5744.generalize);
         letrecs = (uu___133_5744.letrecs);
         top_level = (uu___133_5744.top_level);
         check_uvars = (uu___133_5744.check_uvars);
         use_eq = (uu___133_5744.use_eq);
         is_iface = (uu___133_5744.is_iface);
         admit = (uu___133_5744.admit);
         lax = (uu___133_5744.lax);
         lax_universes = (uu___133_5744.lax_universes);
         type_of = (uu___133_5744.type_of);
         universe_of = (uu___133_5744.universe_of);
         use_bv_sorts = (uu___133_5744.use_bv_sorts);
         qname_and_index = (uu___133_5744.qname_and_index);
         proof_ns = (uu___133_5744.proof_ns)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5794)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5809 =
            let uu____5813 = FStar_Syntax_Free.uvars t in ext out uu____5813 in
          aux uu____5809 tl1
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
          let uu____5869 =
            let uu____5871 = FStar_Syntax_Free.univs t in ext out uu____5871 in
          aux uu____5869 tl1
      | (Binding_sig uu____5873)::uu____5874 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5911)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5921 = FStar_Util.set_add uname out in aux uu____5921 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5935 =
            let uu____5937 = FStar_Syntax_Free.univnames t in
            ext out uu____5937 in
          aux uu____5935 tl1
      | (Binding_sig uu____5939)::uu____5940 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_5956  ->
            match uu___112_5956 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5968 =
      let uu____5970 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____5970
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____5968 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____5986 =
      let uu____5987 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_5991  ->
                match uu___113_5991 with
                | Binding_var x ->
                    let uu____5993 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____5993
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____5996) ->
                    let uu____5997 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____5997
                | Binding_sig (ls,uu____5999) ->
                    let uu____6002 =
                      let uu____6003 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6003
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6002
                | Binding_sig_inst (ls,uu____6009,uu____6010) ->
                    let uu____6013 =
                      let uu____6014 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6014
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6013)) in
      FStar_All.pipe_right uu____5987 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____5986 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6026 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6026
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6043  ->
                 fun uu____6044  ->
                   match (uu____6043, uu____6044) with
                   | ((b1,uu____6054),(b2,uu____6056)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_6099  ->
             match uu___114_6099 with
             | Binding_sig (lids,uu____6103) -> FStar_List.append lids keys
             | uu____6106 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6108  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6133) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6145,uu____6146) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6170 = list_prefix p path1 in
            if uu____6170 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6180 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____6180
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_6200 = e in
            {
              solver = (uu___134_6200.solver);
              range = (uu___134_6200.range);
              curmodule = (uu___134_6200.curmodule);
              gamma = (uu___134_6200.gamma);
              gamma_cache = (uu___134_6200.gamma_cache);
              modules = (uu___134_6200.modules);
              expected_typ = (uu___134_6200.expected_typ);
              sigtab = (uu___134_6200.sigtab);
              is_pattern = (uu___134_6200.is_pattern);
              instantiate_imp = (uu___134_6200.instantiate_imp);
              effects = (uu___134_6200.effects);
              generalize = (uu___134_6200.generalize);
              letrecs = (uu___134_6200.letrecs);
              top_level = (uu___134_6200.top_level);
              check_uvars = (uu___134_6200.check_uvars);
              use_eq = (uu___134_6200.use_eq);
              is_iface = (uu___134_6200.is_iface);
              admit = (uu___134_6200.admit);
              lax = (uu___134_6200.lax);
              lax_universes = (uu___134_6200.lax_universes);
              type_of = (uu___134_6200.type_of);
              universe_of = (uu___134_6200.universe_of);
              use_bv_sorts = (uu___134_6200.use_bv_sorts);
              qname_and_index = (uu___134_6200.qname_and_index);
              proof_ns = (pns' :: rest)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_6219 = e in
    {
      solver = (uu___135_6219.solver);
      range = (uu___135_6219.range);
      curmodule = (uu___135_6219.curmodule);
      gamma = (uu___135_6219.gamma);
      gamma_cache = (uu___135_6219.gamma_cache);
      modules = (uu___135_6219.modules);
      expected_typ = (uu___135_6219.expected_typ);
      sigtab = (uu___135_6219.sigtab);
      is_pattern = (uu___135_6219.is_pattern);
      instantiate_imp = (uu___135_6219.instantiate_imp);
      effects = (uu___135_6219.effects);
      generalize = (uu___135_6219.generalize);
      letrecs = (uu___135_6219.letrecs);
      top_level = (uu___135_6219.top_level);
      check_uvars = (uu___135_6219.check_uvars);
      use_eq = (uu___135_6219.use_eq);
      is_iface = (uu___135_6219.is_iface);
      admit = (uu___135_6219.admit);
      lax = (uu___135_6219.lax);
      lax_universes = (uu___135_6219.lax_universes);
      type_of = (uu___135_6219.type_of);
      universe_of = (uu___135_6219.universe_of);
      use_bv_sorts = (uu___135_6219.use_bv_sorts);
      qname_and_index = (uu___135_6219.qname_and_index);
      proof_ns = ([] :: (e.proof_ns))
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6228::rest ->
        let uu___136_6231 = e in
        {
          solver = (uu___136_6231.solver);
          range = (uu___136_6231.range);
          curmodule = (uu___136_6231.curmodule);
          gamma = (uu___136_6231.gamma);
          gamma_cache = (uu___136_6231.gamma_cache);
          modules = (uu___136_6231.modules);
          expected_typ = (uu___136_6231.expected_typ);
          sigtab = (uu___136_6231.sigtab);
          is_pattern = (uu___136_6231.is_pattern);
          instantiate_imp = (uu___136_6231.instantiate_imp);
          effects = (uu___136_6231.effects);
          generalize = (uu___136_6231.generalize);
          letrecs = (uu___136_6231.letrecs);
          top_level = (uu___136_6231.top_level);
          check_uvars = (uu___136_6231.check_uvars);
          use_eq = (uu___136_6231.use_eq);
          is_iface = (uu___136_6231.is_iface);
          admit = (uu___136_6231.admit);
          lax = (uu___136_6231.lax);
          lax_universes = (uu___136_6231.lax_universes);
          type_of = (uu___136_6231.type_of);
          universe_of = (uu___136_6231.universe_of);
          use_bv_sorts = (uu___136_6231.use_bv_sorts);
          qname_and_index = (uu___136_6231.qname_and_index);
          proof_ns = rest
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_6241 = e in
      {
        solver = (uu___137_6241.solver);
        range = (uu___137_6241.range);
        curmodule = (uu___137_6241.curmodule);
        gamma = (uu___137_6241.gamma);
        gamma_cache = (uu___137_6241.gamma_cache);
        modules = (uu___137_6241.modules);
        expected_typ = (uu___137_6241.expected_typ);
        sigtab = (uu___137_6241.sigtab);
        is_pattern = (uu___137_6241.is_pattern);
        instantiate_imp = (uu___137_6241.instantiate_imp);
        effects = (uu___137_6241.effects);
        generalize = (uu___137_6241.generalize);
        letrecs = (uu___137_6241.letrecs);
        top_level = (uu___137_6241.top_level);
        check_uvars = (uu___137_6241.check_uvars);
        use_eq = (uu___137_6241.use_eq);
        is_iface = (uu___137_6241.is_iface);
        admit = (uu___137_6241.admit);
        lax = (uu___137_6241.lax);
        lax_universes = (uu___137_6241.lax_universes);
        type_of = (uu___137_6241.type_of);
        universe_of = (uu___137_6241.universe_of);
        use_bv_sorts = (uu___137_6241.use_bv_sorts);
        qname_and_index = (uu___137_6241.qname_and_index);
        proof_ns = ns
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6259 =
        FStar_List.map
          (fun fpns  ->
             let uu____6270 =
               let uu____6271 =
                 let uu____6272 =
                   FStar_List.map
                     (fun uu____6277  ->
                        match uu____6277 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____6272 in
               Prims.strcat uu____6271 "]" in
             Prims.strcat "[" uu____6270) pns in
      FStar_String.concat ";" uu____6259 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____6286  -> ());
    push = (fun uu____6287  -> ());
    pop = (fun uu____6288  -> ());
    mark = (fun uu____6289  -> ());
    reset_mark = (fun uu____6290  -> ());
    commit_mark = (fun uu____6291  -> ());
    encode_modul = (fun uu____6292  -> fun uu____6293  -> ());
    encode_sig = (fun uu____6294  -> fun uu____6295  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6302  -> fun uu____6303  -> fun uu____6304  -> ());
    is_trivial = (fun uu____6308  -> fun uu____6309  -> false);
    finish = (fun uu____6310  -> ());
    refresh = (fun uu____6311  -> ())
  }