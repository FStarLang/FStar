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
  qname_and_index: (FStar_Ident.lident* Prims.int) option;}
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
      | (NoDelta ,uu____845) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____846,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____847,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____848 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____858 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____866 =
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
          let uu____905 = new_gamma_cache () in
          let uu____907 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____905;
            modules = [];
            expected_typ = None;
            sigtab = uu____907;
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
            qname_and_index = None
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident* Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____950  ->
    let uu____951 = FStar_ST.read query_indices in
    match uu____951 with
    | [] -> failwith "Empty query indices!"
    | uu____965 ->
        let uu____970 =
          let uu____975 =
            let uu____979 = FStar_ST.read query_indices in
            FStar_List.hd uu____979 in
          let uu____993 = FStar_ST.read query_indices in uu____975 ::
            uu____993 in
        FStar_ST.write query_indices uu____970
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1015  ->
    let uu____1016 = FStar_ST.read query_indices in
    match uu____1016 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1052  ->
    match uu____1052 with
    | (l,n1) ->
        let uu____1057 = FStar_ST.read query_indices in
        (match uu____1057 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1091 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1101  ->
    let uu____1102 = FStar_ST.read query_indices in FStar_List.hd uu____1102
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1118  ->
    let uu____1119 = FStar_ST.read query_indices in
    match uu____1119 with
    | hd1::uu____1131::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1158 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1172 =
       let uu____1174 = FStar_ST.read stack in env :: uu____1174 in
     FStar_ST.write stack uu____1172);
    (let uu___112_1182 = env in
     let uu____1183 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1185 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___112_1182.solver);
       range = (uu___112_1182.range);
       curmodule = (uu___112_1182.curmodule);
       gamma = (uu___112_1182.gamma);
       gamma_cache = uu____1183;
       modules = (uu___112_1182.modules);
       expected_typ = (uu___112_1182.expected_typ);
       sigtab = uu____1185;
       is_pattern = (uu___112_1182.is_pattern);
       instantiate_imp = (uu___112_1182.instantiate_imp);
       effects = (uu___112_1182.effects);
       generalize = (uu___112_1182.generalize);
       letrecs = (uu___112_1182.letrecs);
       top_level = (uu___112_1182.top_level);
       check_uvars = (uu___112_1182.check_uvars);
       use_eq = (uu___112_1182.use_eq);
       is_iface = (uu___112_1182.is_iface);
       admit = (uu___112_1182.admit);
       lax = (uu___112_1182.lax);
       lax_universes = (uu___112_1182.lax_universes);
       type_of = (uu___112_1182.type_of);
       universe_of = (uu___112_1182.universe_of);
       use_bv_sorts = (uu___112_1182.use_bv_sorts);
       qname_and_index = (uu___112_1182.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1189  ->
    let uu____1190 = FStar_ST.read stack in
    match uu____1190 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1202 -> failwith "Impossible: Too many pops"
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
    (let uu____1234 = pop_stack () in ());
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
        let uu____1253 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1265  ->
                  match uu____1265 with
                  | (m,uu____1269) -> FStar_Ident.lid_equals l m)) in
        (match uu____1253 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1274 = env in
               {
                 solver = (uu___113_1274.solver);
                 range = (uu___113_1274.range);
                 curmodule = (uu___113_1274.curmodule);
                 gamma = (uu___113_1274.gamma);
                 gamma_cache = (uu___113_1274.gamma_cache);
                 modules = (uu___113_1274.modules);
                 expected_typ = (uu___113_1274.expected_typ);
                 sigtab = (uu___113_1274.sigtab);
                 is_pattern = (uu___113_1274.is_pattern);
                 instantiate_imp = (uu___113_1274.instantiate_imp);
                 effects = (uu___113_1274.effects);
                 generalize = (uu___113_1274.generalize);
                 letrecs = (uu___113_1274.letrecs);
                 top_level = (uu___113_1274.top_level);
                 check_uvars = (uu___113_1274.check_uvars);
                 use_eq = (uu___113_1274.use_eq);
                 is_iface = (uu___113_1274.is_iface);
                 admit = (uu___113_1274.admit);
                 lax = (uu___113_1274.lax);
                 lax_universes = (uu___113_1274.lax_universes);
                 type_of = (uu___113_1274.type_of);
                 universe_of = (uu___113_1274.universe_of);
                 use_bv_sorts = (uu___113_1274.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1277,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___114_1283 = env in
               {
                 solver = (uu___114_1283.solver);
                 range = (uu___114_1283.range);
                 curmodule = (uu___114_1283.curmodule);
                 gamma = (uu___114_1283.gamma);
                 gamma_cache = (uu___114_1283.gamma_cache);
                 modules = (uu___114_1283.modules);
                 expected_typ = (uu___114_1283.expected_typ);
                 sigtab = (uu___114_1283.sigtab);
                 is_pattern = (uu___114_1283.is_pattern);
                 instantiate_imp = (uu___114_1283.instantiate_imp);
                 effects = (uu___114_1283.effects);
                 generalize = (uu___114_1283.generalize);
                 letrecs = (uu___114_1283.letrecs);
                 top_level = (uu___114_1283.top_level);
                 check_uvars = (uu___114_1283.check_uvars);
                 use_eq = (uu___114_1283.use_eq);
                 is_iface = (uu___114_1283.is_iface);
                 admit = (uu___114_1283.admit);
                 lax = (uu___114_1283.lax);
                 lax_universes = (uu___114_1283.lax_universes);
                 type_of = (uu___114_1283.type_of);
                 universe_of = (uu___114_1283.universe_of);
                 use_bv_sorts = (uu___114_1283.use_bv_sorts);
                 qname_and_index = (Some (l, next))
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
        (let uu___115_1299 = e in
         {
           solver = (uu___115_1299.solver);
           range = r;
           curmodule = (uu___115_1299.curmodule);
           gamma = (uu___115_1299.gamma);
           gamma_cache = (uu___115_1299.gamma_cache);
           modules = (uu___115_1299.modules);
           expected_typ = (uu___115_1299.expected_typ);
           sigtab = (uu___115_1299.sigtab);
           is_pattern = (uu___115_1299.is_pattern);
           instantiate_imp = (uu___115_1299.instantiate_imp);
           effects = (uu___115_1299.effects);
           generalize = (uu___115_1299.generalize);
           letrecs = (uu___115_1299.letrecs);
           top_level = (uu___115_1299.top_level);
           check_uvars = (uu___115_1299.check_uvars);
           use_eq = (uu___115_1299.use_eq);
           is_iface = (uu___115_1299.is_iface);
           admit = (uu___115_1299.admit);
           lax = (uu___115_1299.lax);
           lax_universes = (uu___115_1299.lax_universes);
           type_of = (uu___115_1299.type_of);
           universe_of = (uu___115_1299.universe_of);
           use_bv_sorts = (uu___115_1299.use_bv_sorts);
           qname_and_index = (uu___115_1299.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___116_1316 = env in
      {
        solver = (uu___116_1316.solver);
        range = (uu___116_1316.range);
        curmodule = lid;
        gamma = (uu___116_1316.gamma);
        gamma_cache = (uu___116_1316.gamma_cache);
        modules = (uu___116_1316.modules);
        expected_typ = (uu___116_1316.expected_typ);
        sigtab = (uu___116_1316.sigtab);
        is_pattern = (uu___116_1316.is_pattern);
        instantiate_imp = (uu___116_1316.instantiate_imp);
        effects = (uu___116_1316.effects);
        generalize = (uu___116_1316.generalize);
        letrecs = (uu___116_1316.letrecs);
        top_level = (uu___116_1316.top_level);
        check_uvars = (uu___116_1316.check_uvars);
        use_eq = (uu___116_1316.use_eq);
        is_iface = (uu___116_1316.is_iface);
        admit = (uu___116_1316.admit);
        lax = (uu___116_1316.lax);
        lax_universes = (uu___116_1316.lax_universes);
        type_of = (uu___116_1316.type_of);
        universe_of = (uu___116_1316.universe_of);
        use_bv_sorts = (uu___116_1316.use_bv_sorts);
        qname_and_index = (uu___116_1316.qname_and_index)
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
    let uu____1338 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1338
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1341  ->
    let uu____1342 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____1342
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1366) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1382 = FStar_Syntax_Subst.subst vs t in (us, uu____1382)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___100_1387  ->
    match uu___100_1387 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1401  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1411 = inst_tscheme t in
      match uu____1411 with
      | (us,t1) ->
          let uu____1418 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1418)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1430  ->
          match uu____1430 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1444 =
                         let uu____1445 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1448 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1451 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1452 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1445 uu____1448 uu____1451 uu____1452 in
                       failwith uu____1444)
                    else ();
                    (let uu____1454 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     snd uu____1454))
               | uu____1458 ->
                   let uu____1459 =
                     let uu____1460 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1460 in
                   failwith uu____1459)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1464 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1468 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1472 -> false
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
             | ([],uu____1498) -> Maybe
             | (uu____1502,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1514 -> No in
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
          let uu____1574 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1574 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_1595  ->
                   match uu___101_1595 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1618 =
                           let uu____1628 =
                             let uu____1636 = inst_tscheme t in
                             FStar_Util.Inl uu____1636 in
                           (uu____1628, (FStar_Ident.range_of_lid l)) in
                         Some uu____1618
                       else None
                   | Binding_sig
                       (uu____1670,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1672);
                                     FStar_Syntax_Syntax.sigrng = uu____1673;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1674;
                                     FStar_Syntax_Syntax.sigmeta = uu____1675;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1684 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1684
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1711 ->
                             Some t
                         | uu____1715 -> cache t in
                       let uu____1716 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1716 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1756 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1756 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1800 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1842 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1842
         then
           let uu____1853 = find_in_sigtab env lid in
           match uu____1853 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1919) ->
          add_sigelts env ses
      | uu____1924 ->
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
            | uu____1933 -> ()))
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
        (fun uu___102_1951  ->
           match uu___102_1951 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____1964 -> None)
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
          ((uu____1985,lb::[]),uu____1987,uu____1988) ->
          let uu____1997 =
            let uu____2002 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2008 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2002, uu____2008) in
          Some uu____1997
      | FStar_Syntax_Syntax.Sig_let ((uu____2015,lbs),uu____2017,uu____2018)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2038 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2045 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2045
                   then
                     let uu____2051 =
                       let uu____2056 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2062 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2056, uu____2062) in
                     Some uu____2051
                   else None)
      | uu____2074 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2093 =
          let uu____2098 =
            let uu____2101 =
              let uu____2102 =
                let uu____2105 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2105 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2102) in
            inst_tscheme uu____2101 in
          (uu____2098, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2093
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2119,uu____2120) ->
        let uu____2123 =
          let uu____2128 =
            let uu____2131 =
              let uu____2132 =
                let uu____2135 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2135 in
              (us, uu____2132) in
            inst_tscheme uu____2131 in
          (uu____2128, (se.FStar_Syntax_Syntax.sigrng)) in
        Some uu____2123
    | uu____2146 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2181 =
        match uu____2181 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2231,uvs,t,uu____2234,uu____2235,uu____2236);
                    FStar_Syntax_Syntax.sigrng = uu____2237;
                    FStar_Syntax_Syntax.sigquals = uu____2238;
                    FStar_Syntax_Syntax.sigmeta = uu____2239;_},None
                  )
                 ->
                 let uu____2249 =
                   let uu____2254 = inst_tscheme (uvs, t) in
                   (uu____2254, rng) in
                 Some uu____2249
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2266;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2268;_},None
                  )
                 ->
                 let uu____2276 =
                   let uu____2277 = in_cur_mod env l in uu____2277 = Yes in
                 if uu____2276
                 then
                   let uu____2283 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2283
                    then
                      let uu____2290 =
                        let uu____2295 = inst_tscheme (uvs, t) in
                        (uu____2295, rng) in
                      Some uu____2290
                    else None)
                 else
                   (let uu____2310 =
                      let uu____2315 = inst_tscheme (uvs, t) in
                      (uu____2315, rng) in
                    Some uu____2310)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2328,uu____2329);
                    FStar_Syntax_Syntax.sigrng = uu____2330;
                    FStar_Syntax_Syntax.sigquals = uu____2331;
                    FStar_Syntax_Syntax.sigmeta = uu____2332;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2351 =
                        let uu____2356 = inst_tscheme (uvs, k) in
                        (uu____2356, rng) in
                      Some uu____2351
                  | uu____2365 ->
                      let uu____2366 =
                        let uu____2371 =
                          let uu____2374 =
                            let uu____2375 =
                              let uu____2378 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2378 in
                            (uvs, uu____2375) in
                          inst_tscheme uu____2374 in
                        (uu____2371, rng) in
                      Some uu____2366)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2393,uu____2394);
                    FStar_Syntax_Syntax.sigrng = uu____2395;
                    FStar_Syntax_Syntax.sigquals = uu____2396;
                    FStar_Syntax_Syntax.sigmeta = uu____2397;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2417 =
                        let uu____2422 = inst_tscheme_with (uvs, k) us in
                        (uu____2422, rng) in
                      Some uu____2417
                  | uu____2431 ->
                      let uu____2432 =
                        let uu____2437 =
                          let uu____2440 =
                            let uu____2441 =
                              let uu____2444 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2444 in
                            (uvs, uu____2441) in
                          inst_tscheme_with uu____2440 us in
                        (uu____2437, rng) in
                      Some uu____2432)
             | FStar_Util.Inr se ->
                 let uu____2464 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2475;
                        FStar_Syntax_Syntax.sigrng = uu____2476;
                        FStar_Syntax_Syntax.sigquals = uu____2477;
                        FStar_Syntax_Syntax.sigmeta = uu____2478;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2487 -> effect_signature (fst se) in
                 FStar_All.pipe_right uu____2464
                   (FStar_Util.map_option
                      (fun uu____2510  ->
                         match uu____2510 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2527 =
        let uu____2533 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2533 mapper in
      match uu____2527 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___117_2585 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___117_2585.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___117_2585.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___117_2585.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2606 = lookup_qname env l in
      match uu____2606 with | None  -> false | Some uu____2626 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2654 = try_lookup_bv env bv in
      match uu____2654 with
      | None  ->
          let uu____2662 =
            let uu____2663 =
              let uu____2666 = variable_not_found bv in (uu____2666, bvr) in
            FStar_Errors.Error uu____2663 in
          raise uu____2662
      | Some (t,r) ->
          let uu____2673 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2674 = FStar_Range.set_use_range r bvr in
          (uu____2673, uu____2674)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2686 = try_lookup_lid_aux env l in
      match uu____2686 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2728 =
            let uu____2733 =
              let uu____2736 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2736) in
            (uu____2733, r1) in
          Some uu____2728
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2753 = try_lookup_lid env l in
      match uu____2753 with
      | None  ->
          let uu____2767 =
            let uu____2768 =
              let uu____2771 = name_not_found l in
              (uu____2771, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2768 in
          raise uu____2767
      | Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_2792  ->
              match uu___103_2792 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2794 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        option
  =
  fun env  ->
    fun lid  ->
      let uu____2805 = lookup_qname env lid in
      match uu____2805 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2820,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2823;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2825;_},None
            ),uu____2826)
          ->
          let uu____2850 =
            let uu____2856 =
              let uu____2859 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2859) in
            (uu____2856, q) in
          Some uu____2850
      | uu____2868 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2890 = lookup_qname env lid in
      match uu____2890 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2903,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2906;
              FStar_Syntax_Syntax.sigquals = uu____2907;
              FStar_Syntax_Syntax.sigmeta = uu____2908;_},None
            ),uu____2909)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2933 ->
          let uu____2944 =
            let uu____2945 =
              let uu____2948 = name_not_found lid in
              (uu____2948, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____2945 in
          raise uu____2944
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2959 = lookup_qname env lid in
      match uu____2959 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____2972,uvs,t,uu____2975,uu____2976,uu____2977);
              FStar_Syntax_Syntax.sigrng = uu____2978;
              FStar_Syntax_Syntax.sigquals = uu____2979;
              FStar_Syntax_Syntax.sigmeta = uu____2980;_},None
            ),uu____2981)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3007 ->
          let uu____3018 =
            let uu____3019 =
              let uu____3022 = name_not_found lid in
              (uu____3022, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3019 in
          raise uu____3018
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3034 = lookup_qname env lid in
      match uu____3034 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3048,uu____3049,uu____3050,uu____3051,uu____3052,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3054;
              FStar_Syntax_Syntax.sigquals = uu____3055;
              FStar_Syntax_Syntax.sigmeta = uu____3056;_},uu____3057),uu____3058)
          -> (true, dcs)
      | uu____3088 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3106 = lookup_qname env lid in
      match uu____3106 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3117,uu____3118,uu____3119,l,uu____3121,uu____3122);
              FStar_Syntax_Syntax.sigrng = uu____3123;
              FStar_Syntax_Syntax.sigquals = uu____3124;
              FStar_Syntax_Syntax.sigmeta = uu____3125;_},uu____3126),uu____3127)
          -> l
      | uu____3154 ->
          let uu____3165 =
            let uu____3166 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3166 in
          failwith uu____3165
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
        let uu____3190 = lookup_qname env lid in
        match uu____3190 with
        | Some (FStar_Util.Inr (se,None ),uu____3205) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3231,lbs),uu____3233,uu____3234) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3251 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3251
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3272 -> None)
        | uu____3275 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3296 = lookup_qname env ftv in
      match uu____3296 with
      | Some (FStar_Util.Inr (se,None ),uu____3309) ->
          let uu____3332 = effect_signature se in
          (match uu____3332 with
           | None  -> None
           | Some ((uu____3343,t),r) ->
               let uu____3352 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3352)
      | uu____3353 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3370 = try_lookup_effect_lid env ftv in
      match uu____3370 with
      | None  ->
          let uu____3372 =
            let uu____3373 =
              let uu____3376 = name_not_found ftv in
              (uu____3376, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3373 in
          raise uu____3372
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
        let uu____3390 = lookup_qname env lid0 in
        match uu____3390 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3408);
                FStar_Syntax_Syntax.sigrng = uu____3409;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3411;_},None
              ),uu____3412)
            ->
            let lid1 =
              let uu____3439 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3439 in
            let uu____3440 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_3442  ->
                      match uu___104_3442 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3443 -> false)) in
            if uu____3440
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
                     (let uu____3459 =
                        let uu____3460 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3461 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3460 uu____3461 in
                      failwith uu____3459) in
               match (binders, univs1) with
               | ([],uu____3467) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3476,uu____3477::uu____3478::uu____3479) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3482 =
                     let uu____3483 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3484 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3483 uu____3484 in
                   failwith uu____3482
               | uu____3490 ->
                   let uu____3493 =
                     let uu____3496 =
                       let uu____3497 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3497) in
                     inst_tscheme_with uu____3496 insts in
                   (match uu____3493 with
                    | (uu____3505,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3508 =
                          let uu____3509 = FStar_Syntax_Subst.compress t1 in
                          uu____3509.FStar_Syntax_Syntax.n in
                        (match uu____3508 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3539 -> failwith "Impossible")))
        | uu____3543 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3569 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3569 with
        | None  -> None
        | Some (uu____3576,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3581 = find1 l2 in
            (match uu____3581 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3586 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3586 with
        | Some l1 -> l1
        | None  ->
            let uu____3589 = find1 l in
            (match uu____3589 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3601 = lookup_qname env l1 in
      match uu____3601 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3613;
              FStar_Syntax_Syntax.sigrng = uu____3614;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3616;_},uu____3617),uu____3618)
          -> q
      | uu____3643 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3666 =
          let uu____3667 =
            let uu____3668 = FStar_Util.string_of_int i in
            let uu____3669 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3668 uu____3669 in
          failwith uu____3667 in
        let uu____3670 = lookup_datacon env lid in
        match uu____3670 with
        | (uu____3673,t) ->
            let uu____3675 =
              let uu____3676 = FStar_Syntax_Subst.compress t in
              uu____3676.FStar_Syntax_Syntax.n in
            (match uu____3675 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3680) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3701 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i in
                    FStar_All.pipe_right uu____3701 FStar_Pervasives.fst)
             | uu____3706 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3713 = lookup_qname env l in
      match uu____3713 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3724,uu____3725,uu____3726);
              FStar_Syntax_Syntax.sigrng = uu____3727;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3729;_},uu____3730),uu____3731)
          ->
          FStar_Util.for_some
            (fun uu___105_3756  ->
               match uu___105_3756 with
               | FStar_Syntax_Syntax.Projector uu____3757 -> true
               | uu____3760 -> false) quals
      | uu____3761 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3778 = lookup_qname env lid in
      match uu____3778 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3789,uu____3790,uu____3791,uu____3792,uu____3793,uu____3794);
              FStar_Syntax_Syntax.sigrng = uu____3795;
              FStar_Syntax_Syntax.sigquals = uu____3796;
              FStar_Syntax_Syntax.sigmeta = uu____3797;_},uu____3798),uu____3799)
          -> true
      | uu____3826 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3843 = lookup_qname env lid in
      match uu____3843 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3854,uu____3855,uu____3856,uu____3857,uu____3858,uu____3859);
              FStar_Syntax_Syntax.sigrng = uu____3860;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3862;_},uu____3863),uu____3864)
          ->
          FStar_Util.for_some
            (fun uu___106_3893  ->
               match uu___106_3893 with
               | FStar_Syntax_Syntax.RecordType uu____3894 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3899 -> true
               | uu____3904 -> false) quals
      | uu____3905 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3922 = lookup_qname env lid in
      match uu____3922 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3933,uu____3934,uu____3935);
              FStar_Syntax_Syntax.sigrng = uu____3936;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3938;_},uu____3939),uu____3940)
          ->
          FStar_Util.for_some
            (fun uu___107_3969  ->
               match uu___107_3969 with
               | FStar_Syntax_Syntax.Action uu____3970 -> true
               | uu____3971 -> false) quals
      | uu____3972 -> false
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
      let uu____3991 =
        let uu____3992 = FStar_Syntax_Util.un_uinst head1 in
        uu____3992.FStar_Syntax_Syntax.n in
      match uu____3991 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3996 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4034 -> Some false
        | FStar_Util.Inr (se,uu____4043) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4052 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4056 -> Some true
             | uu____4065 -> Some false) in
      let uu____4066 =
        let uu____4068 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4068 mapper in
      match uu____4066 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4095 = lookup_qname env lid in
      match uu____4095 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4106,uu____4107,tps,uu____4109,uu____4110,uu____4111);
              FStar_Syntax_Syntax.sigrng = uu____4112;
              FStar_Syntax_Syntax.sigquals = uu____4113;
              FStar_Syntax_Syntax.sigmeta = uu____4114;_},uu____4115),uu____4116)
          -> FStar_List.length tps
      | uu____4148 ->
          let uu____4159 =
            let uu____4160 =
              let uu____4163 = name_not_found lid in
              (uu____4163, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4160 in
          raise uu____4159
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
           (fun uu____4185  ->
              match uu____4185 with
              | (d,uu____4190) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4199 = effect_decl_opt env l in
      match uu____4199 with
      | None  ->
          let uu____4207 =
            let uu____4208 =
              let uu____4211 = name_not_found l in
              (uu____4211, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4208 in
          raise uu____4207
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
            (let uu____4254 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4278  ->
                       match uu____4278 with
                       | (m1,m2,uu____4286,uu____4287,uu____4288) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4254 with
             | None  ->
                 let uu____4297 =
                   let uu____4298 =
                     let uu____4301 =
                       let uu____4302 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4303 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4302
                         uu____4303 in
                     (uu____4301, (env.range)) in
                   FStar_Errors.Error uu____4298 in
                 raise uu____4297
             | Some (uu____4307,uu____4308,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____4355 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4367  ->
            match uu____4367 with
            | (d,uu____4371) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4355 with
  | None  ->
      let uu____4378 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4378
  | Some (md,_q) ->
      let uu____4387 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4387 with
       | (uu____4394,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4402)::(wp,uu____4404)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4426 -> failwith "Impossible"))
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
                 let uu____4462 = get_range env in
                 let uu____4463 =
                   let uu____4466 =
                     let uu____4467 =
                       let uu____4477 =
                         let uu____4479 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4479] in
                       (null_wp, uu____4477) in
                     FStar_Syntax_Syntax.Tm_app uu____4467 in
                   FStar_Syntax_Syntax.mk uu____4466 in
                 uu____4463 None uu____4462 in
               let uu____4489 =
                 let uu____4490 =
                   let uu____4496 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4496] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4490;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4489)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___118_4505 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___118_4505.order);
              joins = (uu___118_4505.joins)
            } in
          let uu___119_4510 = env in
          {
            solver = (uu___119_4510.solver);
            range = (uu___119_4510.range);
            curmodule = (uu___119_4510.curmodule);
            gamma = (uu___119_4510.gamma);
            gamma_cache = (uu___119_4510.gamma_cache);
            modules = (uu___119_4510.modules);
            expected_typ = (uu___119_4510.expected_typ);
            sigtab = (uu___119_4510.sigtab);
            is_pattern = (uu___119_4510.is_pattern);
            instantiate_imp = (uu___119_4510.instantiate_imp);
            effects;
            generalize = (uu___119_4510.generalize);
            letrecs = (uu___119_4510.letrecs);
            top_level = (uu___119_4510.top_level);
            check_uvars = (uu___119_4510.check_uvars);
            use_eq = (uu___119_4510.use_eq);
            is_iface = (uu___119_4510.is_iface);
            admit = (uu___119_4510.admit);
            lax = (uu___119_4510.lax);
            lax_universes = (uu___119_4510.lax_universes);
            type_of = (uu___119_4510.type_of);
            universe_of = (uu___119_4510.universe_of);
            use_bv_sorts = (uu___119_4510.use_bv_sorts);
            qname_and_index = (uu___119_4510.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4527 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4527 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4606 = (e1.mlift).mlift_wp t wp in
                              let uu____4607 = l1 t wp e in
                              l2 t uu____4606 uu____4607))
                | uu____4608 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4643 = inst_tscheme lift_t in
            match uu____4643 with
            | (uu____4648,lift_t1) ->
                let uu____4650 =
                  let uu____4653 =
                    let uu____4654 =
                      let uu____4664 =
                        let uu____4666 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4667 =
                          let uu____4669 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4669] in
                        uu____4666 :: uu____4667 in
                      (lift_t1, uu____4664) in
                    FStar_Syntax_Syntax.Tm_app uu____4654 in
                  FStar_Syntax_Syntax.mk uu____4653 in
                uu____4650 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4714 = inst_tscheme lift_t in
            match uu____4714 with
            | (uu____4719,lift_t1) ->
                let uu____4721 =
                  let uu____4724 =
                    let uu____4725 =
                      let uu____4735 =
                        let uu____4737 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4738 =
                          let uu____4740 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4741 =
                            let uu____4743 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4743] in
                          uu____4740 :: uu____4741 in
                        uu____4737 :: uu____4738 in
                      (lift_t1, uu____4735) in
                    FStar_Syntax_Syntax.Tm_app uu____4725 in
                  FStar_Syntax_Syntax.mk uu____4724 in
                uu____4721 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4784 =
                let uu____4785 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4785
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4784 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4789 =
              let uu____4790 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4790 in
            let uu____4791 =
              let uu____4792 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4807 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4807) in
              FStar_Util.dflt "none" uu____4792 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4789
              uu____4791 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4820  ->
                    match uu____4820 with
                    | (e,uu____4825) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4838 =
            match uu____4838 with
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
              let uu____4863 =
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
                                    (let uu____4875 =
                                       let uu____4880 =
                                         find_edge order1 (i, k) in
                                       let uu____4882 =
                                         find_edge order1 (k, j) in
                                       (uu____4880, uu____4882) in
                                     match uu____4875 with
                                     | (Some e1,Some e2) ->
                                         let uu____4891 = compose_edges e1 e2 in
                                         [uu____4891]
                                     | uu____4892 -> []))))) in
              FStar_List.append order1 uu____4863 in
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
                   let uu____4907 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4908 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4908
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4907
                   then
                     let uu____4911 =
                       let uu____4912 =
                         let uu____4915 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4916 = get_range env in
                         (uu____4915, uu____4916) in
                       FStar_Errors.Error uu____4912 in
                     raise uu____4911
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
                                            let uu____4979 =
                                              let uu____4984 =
                                                find_edge order2 (i, k) in
                                              let uu____4986 =
                                                find_edge order2 (j, k) in
                                              (uu____4984, uu____4986) in
                                            match uu____4979 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5009,uu____5010)
                                                     ->
                                                     let uu____5014 =
                                                       let uu____5017 =
                                                         let uu____5018 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5018 in
                                                       let uu____5020 =
                                                         let uu____5021 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5021 in
                                                       (uu____5017,
                                                         uu____5020) in
                                                     (match uu____5014 with
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
                                            | uu____5040 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___120_5079 = env.effects in
              { decls = (uu___120_5079.decls); order = order2; joins } in
            let uu___121_5080 = env in
            {
              solver = (uu___121_5080.solver);
              range = (uu___121_5080.range);
              curmodule = (uu___121_5080.curmodule);
              gamma = (uu___121_5080.gamma);
              gamma_cache = (uu___121_5080.gamma_cache);
              modules = (uu___121_5080.modules);
              expected_typ = (uu___121_5080.expected_typ);
              sigtab = (uu___121_5080.sigtab);
              is_pattern = (uu___121_5080.is_pattern);
              instantiate_imp = (uu___121_5080.instantiate_imp);
              effects;
              generalize = (uu___121_5080.generalize);
              letrecs = (uu___121_5080.letrecs);
              top_level = (uu___121_5080.top_level);
              check_uvars = (uu___121_5080.check_uvars);
              use_eq = (uu___121_5080.use_eq);
              is_iface = (uu___121_5080.is_iface);
              admit = (uu___121_5080.admit);
              lax = (uu___121_5080.lax);
              lax_universes = (uu___121_5080.lax_universes);
              type_of = (uu___121_5080.type_of);
              universe_of = (uu___121_5080.universe_of);
              use_bv_sorts = (uu___121_5080.use_bv_sorts);
              qname_and_index = (uu___121_5080.qname_and_index)
            }))
      | uu____5081 -> env
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
        | uu____5103 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5111 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5111 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5121 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5121 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5138 =
                     let uu____5139 =
                       let uu____5142 =
                         let uu____5143 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5149 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5157 =
                           let uu____5158 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5158 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5143 uu____5149 uu____5157 in
                       (uu____5142, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5139 in
                   raise uu____5138)
                else ();
                (let inst1 =
                   let uu____5162 =
                     let uu____5168 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5168 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5175  ->
                        fun uu____5176  ->
                          match (uu____5175, uu____5176) with
                          | ((x,uu____5190),(t,uu____5192)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5162 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5207 =
                     let uu___122_5208 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___122_5208.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___122_5208.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___122_5208.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___122_5208.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5207
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5238 =
    let uu____5243 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5243 in
  match uu____5238 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5259 =
        only_reifiable &&
          (let uu____5260 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5260) in
      if uu____5259
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5273 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5275 =
               let uu____5284 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5284) in
             (match uu____5275 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5318 =
                    let uu____5321 = get_range env in
                    let uu____5322 =
                      let uu____5325 =
                        let uu____5326 =
                          let uu____5336 =
                            let uu____5338 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5338; wp] in
                          (repr, uu____5336) in
                        FStar_Syntax_Syntax.Tm_app uu____5326 in
                      FStar_Syntax_Syntax.mk uu____5325 in
                    uu____5322 None uu____5321 in
                  Some uu____5318))
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
          let uu____5382 =
            let uu____5383 =
              let uu____5386 =
                let uu____5387 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5387 in
              let uu____5388 = get_range env in (uu____5386, uu____5388) in
            FStar_Errors.Error uu____5383 in
          raise uu____5382 in
        let uu____5389 = effect_repr_aux true env c u_c in
        match uu____5389 with
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
        | FStar_Util.Inr (eff_name,uu____5421) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5434 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5441 =
        let uu____5442 = FStar_Syntax_Subst.compress t in
        uu____5442.FStar_Syntax_Syntax.n in
      match uu____5441 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5445,c) ->
          is_reifiable_comp env c
      | uu____5457 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5475)::uu____5476 -> x :: rest
        | (Binding_sig_inst uu____5481)::uu____5482 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5491 = push1 x rest1 in local :: uu____5491 in
      let uu___123_5493 = env in
      let uu____5494 = push1 s env.gamma in
      {
        solver = (uu___123_5493.solver);
        range = (uu___123_5493.range);
        curmodule = (uu___123_5493.curmodule);
        gamma = uu____5494;
        gamma_cache = (uu___123_5493.gamma_cache);
        modules = (uu___123_5493.modules);
        expected_typ = (uu___123_5493.expected_typ);
        sigtab = (uu___123_5493.sigtab);
        is_pattern = (uu___123_5493.is_pattern);
        instantiate_imp = (uu___123_5493.instantiate_imp);
        effects = (uu___123_5493.effects);
        generalize = (uu___123_5493.generalize);
        letrecs = (uu___123_5493.letrecs);
        top_level = (uu___123_5493.top_level);
        check_uvars = (uu___123_5493.check_uvars);
        use_eq = (uu___123_5493.use_eq);
        is_iface = (uu___123_5493.is_iface);
        admit = (uu___123_5493.admit);
        lax = (uu___123_5493.lax);
        lax_universes = (uu___123_5493.lax_universes);
        type_of = (uu___123_5493.type_of);
        universe_of = (uu___123_5493.universe_of);
        use_bv_sorts = (uu___123_5493.use_bv_sorts);
        qname_and_index = (uu___123_5493.qname_and_index)
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
      let uu___124_5521 = env in
      {
        solver = (uu___124_5521.solver);
        range = (uu___124_5521.range);
        curmodule = (uu___124_5521.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___124_5521.gamma_cache);
        modules = (uu___124_5521.modules);
        expected_typ = (uu___124_5521.expected_typ);
        sigtab = (uu___124_5521.sigtab);
        is_pattern = (uu___124_5521.is_pattern);
        instantiate_imp = (uu___124_5521.instantiate_imp);
        effects = (uu___124_5521.effects);
        generalize = (uu___124_5521.generalize);
        letrecs = (uu___124_5521.letrecs);
        top_level = (uu___124_5521.top_level);
        check_uvars = (uu___124_5521.check_uvars);
        use_eq = (uu___124_5521.use_eq);
        is_iface = (uu___124_5521.is_iface);
        admit = (uu___124_5521.admit);
        lax = (uu___124_5521.lax);
        lax_universes = (uu___124_5521.lax_universes);
        type_of = (uu___124_5521.type_of);
        universe_of = (uu___124_5521.universe_of);
        use_bv_sorts = (uu___124_5521.use_bv_sorts);
        qname_and_index = (uu___124_5521.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv: env -> (FStar_Syntax_Syntax.bv* env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___125_5542 = env in
             {
               solver = (uu___125_5542.solver);
               range = (uu___125_5542.range);
               curmodule = (uu___125_5542.curmodule);
               gamma = rest;
               gamma_cache = (uu___125_5542.gamma_cache);
               modules = (uu___125_5542.modules);
               expected_typ = (uu___125_5542.expected_typ);
               sigtab = (uu___125_5542.sigtab);
               is_pattern = (uu___125_5542.is_pattern);
               instantiate_imp = (uu___125_5542.instantiate_imp);
               effects = (uu___125_5542.effects);
               generalize = (uu___125_5542.generalize);
               letrecs = (uu___125_5542.letrecs);
               top_level = (uu___125_5542.top_level);
               check_uvars = (uu___125_5542.check_uvars);
               use_eq = (uu___125_5542.use_eq);
               is_iface = (uu___125_5542.is_iface);
               admit = (uu___125_5542.admit);
               lax = (uu___125_5542.lax);
               lax_universes = (uu___125_5542.lax_universes);
               type_of = (uu___125_5542.type_of);
               universe_of = (uu___125_5542.universe_of);
               use_bv_sorts = (uu___125_5542.use_bv_sorts);
               qname_and_index = (uu___125_5542.qname_and_index)
             }))
    | uu____5543 -> None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5556  ->
             match uu____5556 with | (x,uu____5560) -> push_bv env1 x) env bs
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
            let uu___126_5580 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___126_5580.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___126_5580.FStar_Syntax_Syntax.index);
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
      (let uu___127_5610 = env in
       {
         solver = (uu___127_5610.solver);
         range = (uu___127_5610.range);
         curmodule = (uu___127_5610.curmodule);
         gamma = [];
         gamma_cache = (uu___127_5610.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___127_5610.sigtab);
         is_pattern = (uu___127_5610.is_pattern);
         instantiate_imp = (uu___127_5610.instantiate_imp);
         effects = (uu___127_5610.effects);
         generalize = (uu___127_5610.generalize);
         letrecs = (uu___127_5610.letrecs);
         top_level = (uu___127_5610.top_level);
         check_uvars = (uu___127_5610.check_uvars);
         use_eq = (uu___127_5610.use_eq);
         is_iface = (uu___127_5610.is_iface);
         admit = (uu___127_5610.admit);
         lax = (uu___127_5610.lax);
         lax_universes = (uu___127_5610.lax_universes);
         type_of = (uu___127_5610.type_of);
         universe_of = (uu___127_5610.universe_of);
         use_bv_sorts = (uu___127_5610.use_bv_sorts);
         qname_and_index = (uu___127_5610.qname_and_index)
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
        let uu____5634 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5634 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5650 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5650)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___128_5660 = env in
      {
        solver = (uu___128_5660.solver);
        range = (uu___128_5660.range);
        curmodule = (uu___128_5660.curmodule);
        gamma = (uu___128_5660.gamma);
        gamma_cache = (uu___128_5660.gamma_cache);
        modules = (uu___128_5660.modules);
        expected_typ = (Some t);
        sigtab = (uu___128_5660.sigtab);
        is_pattern = (uu___128_5660.is_pattern);
        instantiate_imp = (uu___128_5660.instantiate_imp);
        effects = (uu___128_5660.effects);
        generalize = (uu___128_5660.generalize);
        letrecs = (uu___128_5660.letrecs);
        top_level = (uu___128_5660.top_level);
        check_uvars = (uu___128_5660.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5660.is_iface);
        admit = (uu___128_5660.admit);
        lax = (uu___128_5660.lax);
        lax_universes = (uu___128_5660.lax_universes);
        type_of = (uu___128_5660.type_of);
        universe_of = (uu___128_5660.universe_of);
        use_bv_sorts = (uu___128_5660.use_bv_sorts);
        qname_and_index = (uu___128_5660.qname_and_index)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5676 = expected_typ env_ in
    ((let uu___129_5679 = env_ in
      {
        solver = (uu___129_5679.solver);
        range = (uu___129_5679.range);
        curmodule = (uu___129_5679.curmodule);
        gamma = (uu___129_5679.gamma);
        gamma_cache = (uu___129_5679.gamma_cache);
        modules = (uu___129_5679.modules);
        expected_typ = None;
        sigtab = (uu___129_5679.sigtab);
        is_pattern = (uu___129_5679.is_pattern);
        instantiate_imp = (uu___129_5679.instantiate_imp);
        effects = (uu___129_5679.effects);
        generalize = (uu___129_5679.generalize);
        letrecs = (uu___129_5679.letrecs);
        top_level = (uu___129_5679.top_level);
        check_uvars = (uu___129_5679.check_uvars);
        use_eq = false;
        is_iface = (uu___129_5679.is_iface);
        admit = (uu___129_5679.admit);
        lax = (uu___129_5679.lax);
        lax_universes = (uu___129_5679.lax_universes);
        type_of = (uu___129_5679.type_of);
        universe_of = (uu___129_5679.universe_of);
        use_bv_sorts = (uu___129_5679.use_bv_sorts);
        qname_and_index = (uu___129_5679.qname_and_index)
      }), uu____5676)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5690 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5694  ->
                    match uu___108_5694 with
                    | Binding_sig (uu____5696,se) -> [se]
                    | uu____5700 -> [])) in
          FStar_All.pipe_right uu____5690 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___130_5705 = env in
       {
         solver = (uu___130_5705.solver);
         range = (uu___130_5705.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___130_5705.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___130_5705.expected_typ);
         sigtab = (uu___130_5705.sigtab);
         is_pattern = (uu___130_5705.is_pattern);
         instantiate_imp = (uu___130_5705.instantiate_imp);
         effects = (uu___130_5705.effects);
         generalize = (uu___130_5705.generalize);
         letrecs = (uu___130_5705.letrecs);
         top_level = (uu___130_5705.top_level);
         check_uvars = (uu___130_5705.check_uvars);
         use_eq = (uu___130_5705.use_eq);
         is_iface = (uu___130_5705.is_iface);
         admit = (uu___130_5705.admit);
         lax = (uu___130_5705.lax);
         lax_universes = (uu___130_5705.lax_universes);
         type_of = (uu___130_5705.type_of);
         universe_of = (uu___130_5705.universe_of);
         use_bv_sorts = (uu___130_5705.use_bv_sorts);
         qname_and_index = (uu___130_5705.qname_and_index)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5755)::tl1 -> aux out tl1
      | (Binding_lid (uu____5758,(uu____5759,t)))::tl1 ->
          let uu____5768 =
            let uu____5772 = FStar_Syntax_Free.uvars t in ext out uu____5772 in
          aux uu____5768 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5776;
            FStar_Syntax_Syntax.index = uu____5777;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5783 =
            let uu____5787 = FStar_Syntax_Free.uvars t in ext out uu____5787 in
          aux uu____5783 tl1
      | (Binding_sig uu____5791)::uu____5792 -> out
      | (Binding_sig_inst uu____5797)::uu____5798 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5835)::tl1 -> aux out tl1
      | (Binding_univ uu____5842)::tl1 -> aux out tl1
      | (Binding_lid (uu____5845,(uu____5846,t)))::tl1 ->
          let uu____5855 =
            let uu____5857 = FStar_Syntax_Free.univs t in ext out uu____5857 in
          aux uu____5855 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5859;
            FStar_Syntax_Syntax.index = uu____5860;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5866 =
            let uu____5868 = FStar_Syntax_Free.univs t in ext out uu____5868 in
          aux uu____5866 tl1
      | (Binding_sig uu____5870)::uu____5871 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5908)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5918 = FStar_Util.set_add uname out in aux uu____5918 tl1
      | (Binding_lid (uu____5920,(uu____5921,t)))::tl1 ->
          let uu____5930 =
            let uu____5932 = FStar_Syntax_Free.univnames t in
            ext out uu____5932 in
          aux uu____5930 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5934;
            FStar_Syntax_Syntax.index = uu____5935;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5941 =
            let uu____5943 = FStar_Syntax_Free.univnames t in
            ext out uu____5943 in
          aux uu____5941 tl1
      | (Binding_sig uu____5945)::uu____5946 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___109_5962  ->
            match uu___109_5962 with
            | Binding_var x -> [x]
            | Binding_lid uu____5965 -> []
            | Binding_sig uu____5968 -> []
            | Binding_univ uu____5972 -> []
            | Binding_sig_inst uu____5973 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5983 =
      let uu____5985 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____5985
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____5983 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6001 =
      let uu____6002 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___110_6006  ->
                match uu___110_6006 with
                | Binding_var x ->
                    let uu____6008 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6008
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6011) ->
                    let uu____6012 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6012
                | Binding_sig (ls,uu____6014) ->
                    let uu____6017 =
                      let uu____6018 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6018
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6017
                | Binding_sig_inst (ls,uu____6024,uu____6025) ->
                    let uu____6028 =
                      let uu____6029 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6029
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6028)) in
      FStar_All.pipe_right uu____6002 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6001 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6041 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6041
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6058  ->
                 fun uu____6059  ->
                   match (uu____6058, uu____6059) with
                   | ((b1,uu____6069),(b2,uu____6071)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___111_6114  ->
             match uu___111_6114 with
             | Binding_sig (lids,uu____6118) -> FStar_List.append lids keys
             | uu____6121 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6123  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6127  -> ());
    push = (fun uu____6128  -> ());
    pop = (fun uu____6129  -> ());
    mark = (fun uu____6130  -> ());
    reset_mark = (fun uu____6131  -> ());
    commit_mark = (fun uu____6132  -> ());
    encode_modul = (fun uu____6133  -> fun uu____6134  -> ());
    encode_sig = (fun uu____6135  -> fun uu____6136  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6143  -> fun uu____6144  -> fun uu____6145  -> ());
    is_trivial = (fun uu____6149  -> fun uu____6150  -> false);
    finish = (fun uu____6151  -> ());
    refresh = (fun uu____6152  -> ())
  }