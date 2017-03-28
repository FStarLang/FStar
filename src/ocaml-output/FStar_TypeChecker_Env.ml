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
  decls: FStar_Syntax_Syntax.eff_decl Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident* FStar_Ident.lident* FStar_Ident.lident* mlift*
      mlift) Prims.list;}
type cached_elt =
  (((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt*
                                                               FStar_Syntax_Syntax.universes
                                                               Prims.option))
    FStar_Util.either* FStar_Range.range)
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
  qname_and_index: (FStar_Ident.lident* Prims.int) Prims.option;}
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
      | uu____809 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____819 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____827 =
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
          let uu____866 = new_gamma_cache () in
          let uu____868 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____866;
            modules = [];
            expected_typ = None;
            sigtab = uu____868;
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
  fun uu____908  ->
    let uu____909 = FStar_ST.read query_indices in
    match uu____909 with
    | [] -> failwith "Empty query indices!"
    | uu____923 ->
        let uu____928 =
          let uu____933 =
            let uu____937 = FStar_ST.read query_indices in
            FStar_List.hd uu____937 in
          let uu____951 = FStar_ST.read query_indices in uu____933 ::
            uu____951 in
        FStar_ST.write query_indices uu____928
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____973  ->
    let uu____974 = FStar_ST.read query_indices in
    match uu____974 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index: (FStar_Ident.lident* Prims.int) -> Prims.unit =
  fun uu____1010  ->
    match uu____1010 with
    | (l,n1) ->
        let uu____1015 = FStar_ST.read query_indices in
        (match uu____1015 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1049 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit -> (FStar_Ident.lident* Prims.int) Prims.list =
  fun uu____1059  ->
    let uu____1060 = FStar_ST.read query_indices in FStar_List.hd uu____1060
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1076  ->
    let uu____1077 = FStar_ST.read query_indices in
    match uu____1077 with
    | hd1::uu____1089::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1116 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1130 =
       let uu____1132 = FStar_ST.read stack in env :: uu____1132 in
     FStar_ST.write stack uu____1130);
    (let uu___105_1140 = env in
     let uu____1141 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1143 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___105_1140.solver);
       range = (uu___105_1140.range);
       curmodule = (uu___105_1140.curmodule);
       gamma = (uu___105_1140.gamma);
       gamma_cache = uu____1141;
       modules = (uu___105_1140.modules);
       expected_typ = (uu___105_1140.expected_typ);
       sigtab = uu____1143;
       is_pattern = (uu___105_1140.is_pattern);
       instantiate_imp = (uu___105_1140.instantiate_imp);
       effects = (uu___105_1140.effects);
       generalize = (uu___105_1140.generalize);
       letrecs = (uu___105_1140.letrecs);
       top_level = (uu___105_1140.top_level);
       check_uvars = (uu___105_1140.check_uvars);
       use_eq = (uu___105_1140.use_eq);
       is_iface = (uu___105_1140.is_iface);
       admit = (uu___105_1140.admit);
       lax = (uu___105_1140.lax);
       lax_universes = (uu___105_1140.lax_universes);
       type_of = (uu___105_1140.type_of);
       universe_of = (uu___105_1140.universe_of);
       use_bv_sorts = (uu___105_1140.use_bv_sorts);
       qname_and_index = (uu___105_1140.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1147  ->
    let uu____1148 = FStar_ST.read stack in
    match uu____1148 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1160 -> failwith "Impossible: Too many pops"
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
    (let uu____1192 = pop_stack () in ());
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
        let uu____1211 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1223  ->
                  match uu____1223 with
                  | (m,uu____1227) -> FStar_Ident.lid_equals l m)) in
        (match uu____1211 with
         | None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___106_1232 = env in
               {
                 solver = (uu___106_1232.solver);
                 range = (uu___106_1232.range);
                 curmodule = (uu___106_1232.curmodule);
                 gamma = (uu___106_1232.gamma);
                 gamma_cache = (uu___106_1232.gamma_cache);
                 modules = (uu___106_1232.modules);
                 expected_typ = (uu___106_1232.expected_typ);
                 sigtab = (uu___106_1232.sigtab);
                 is_pattern = (uu___106_1232.is_pattern);
                 instantiate_imp = (uu___106_1232.instantiate_imp);
                 effects = (uu___106_1232.effects);
                 generalize = (uu___106_1232.generalize);
                 letrecs = (uu___106_1232.letrecs);
                 top_level = (uu___106_1232.top_level);
                 check_uvars = (uu___106_1232.check_uvars);
                 use_eq = (uu___106_1232.use_eq);
                 is_iface = (uu___106_1232.is_iface);
                 admit = (uu___106_1232.admit);
                 lax = (uu___106_1232.lax);
                 lax_universes = (uu___106_1232.lax_universes);
                 type_of = (uu___106_1232.type_of);
                 universe_of = (uu___106_1232.universe_of);
                 use_bv_sorts = (uu___106_1232.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1235,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___107_1241 = env in
               {
                 solver = (uu___107_1241.solver);
                 range = (uu___107_1241.range);
                 curmodule = (uu___107_1241.curmodule);
                 gamma = (uu___107_1241.gamma);
                 gamma_cache = (uu___107_1241.gamma_cache);
                 modules = (uu___107_1241.modules);
                 expected_typ = (uu___107_1241.expected_typ);
                 sigtab = (uu___107_1241.sigtab);
                 is_pattern = (uu___107_1241.is_pattern);
                 instantiate_imp = (uu___107_1241.instantiate_imp);
                 effects = (uu___107_1241.effects);
                 generalize = (uu___107_1241.generalize);
                 letrecs = (uu___107_1241.letrecs);
                 top_level = (uu___107_1241.top_level);
                 check_uvars = (uu___107_1241.check_uvars);
                 use_eq = (uu___107_1241.use_eq);
                 is_iface = (uu___107_1241.is_iface);
                 admit = (uu___107_1241.admit);
                 lax = (uu___107_1241.lax);
                 lax_universes = (uu___107_1241.lax_universes);
                 type_of = (uu___107_1241.type_of);
                 universe_of = (uu___107_1241.universe_of);
                 use_bv_sorts = (uu___107_1241.use_bv_sorts);
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
        (let uu___108_1257 = e in
         {
           solver = (uu___108_1257.solver);
           range = r;
           curmodule = (uu___108_1257.curmodule);
           gamma = (uu___108_1257.gamma);
           gamma_cache = (uu___108_1257.gamma_cache);
           modules = (uu___108_1257.modules);
           expected_typ = (uu___108_1257.expected_typ);
           sigtab = (uu___108_1257.sigtab);
           is_pattern = (uu___108_1257.is_pattern);
           instantiate_imp = (uu___108_1257.instantiate_imp);
           effects = (uu___108_1257.effects);
           generalize = (uu___108_1257.generalize);
           letrecs = (uu___108_1257.letrecs);
           top_level = (uu___108_1257.top_level);
           check_uvars = (uu___108_1257.check_uvars);
           use_eq = (uu___108_1257.use_eq);
           is_iface = (uu___108_1257.is_iface);
           admit = (uu___108_1257.admit);
           lax = (uu___108_1257.lax);
           lax_universes = (uu___108_1257.lax_universes);
           type_of = (uu___108_1257.type_of);
           universe_of = (uu___108_1257.universe_of);
           use_bv_sorts = (uu___108_1257.use_bv_sorts);
           qname_and_index = (uu___108_1257.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___109_1274 = env in
      {
        solver = (uu___109_1274.solver);
        range = (uu___109_1274.range);
        curmodule = lid;
        gamma = (uu___109_1274.gamma);
        gamma_cache = (uu___109_1274.gamma_cache);
        modules = (uu___109_1274.modules);
        expected_typ = (uu___109_1274.expected_typ);
        sigtab = (uu___109_1274.sigtab);
        is_pattern = (uu___109_1274.is_pattern);
        instantiate_imp = (uu___109_1274.instantiate_imp);
        effects = (uu___109_1274.effects);
        generalize = (uu___109_1274.generalize);
        letrecs = (uu___109_1274.letrecs);
        top_level = (uu___109_1274.top_level);
        check_uvars = (uu___109_1274.check_uvars);
        use_eq = (uu___109_1274.use_eq);
        is_iface = (uu___109_1274.is_iface);
        admit = (uu___109_1274.admit);
        lax = (uu___109_1274.lax);
        lax_universes = (uu___109_1274.lax_universes);
        type_of = (uu___109_1274.type_of);
        universe_of = (uu___109_1274.universe_of);
        use_bv_sorts = (uu___109_1274.use_bv_sorts);
        qname_and_index = (uu___109_1274.qname_and_index)
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
    let uu____1296 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1296
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1299  ->
    let uu____1300 = FStar_Unionfind.fresh None in
    FStar_Syntax_Syntax.U_unif uu____1300
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1323) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1339 = FStar_Syntax_Subst.subst vs t in (us, uu____1339)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun uu___94_1344  ->
    match uu___94_1344 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1358  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1368 = inst_tscheme t in
      match uu____1368 with
      | (us,t1) ->
          let uu____1375 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1375)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1387  ->
          match uu____1387 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1401 =
                         let uu____1402 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1405 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1408 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1409 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1402 uu____1405 uu____1408 uu____1409 in
                       failwith uu____1401)
                    else ();
                    (let uu____1411 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     Prims.snd uu____1411))
               | uu____1415 ->
                   let uu____1416 =
                     let uu____1417 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1417 in
                   failwith uu____1416)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1421 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1425 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1429 -> false
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
             | ([],uu____1455) -> Maybe
             | (uu____1459,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1471 -> No in
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
          let uu____1531 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1531 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___95_1552  ->
                   match uu___95_1552 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1575 =
                           let uu____1585 =
                             let uu____1593 = inst_tscheme t in
                             FStar_Util.Inl uu____1593 in
                           (uu____1585, (FStar_Ident.range_of_lid l)) in
                         Some uu____1575
                       else None
                   | Binding_sig
                       (uu____1627,FStar_Syntax_Syntax.Sig_bundle
                        (ses,uu____1629,uu____1630,uu____1631))
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1641 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1641
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1668 ->
                             Some t
                         | uu____1675 -> cache t in
                       let uu____1676 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1676 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1716 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1716 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1760 -> None)
          | se -> se
        else None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1802 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1802
         then
           let uu____1813 = find_in_sigtab env lid in
           match uu____1813 with
           | Some se ->
               Some
                 ((FStar_Util.Inr (se, None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | None  -> None
         else None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1879,uu____1880,uu____1881)
          -> add_sigelts env ses
      | uu____1888 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se with
            | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1894) ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____1898 -> ()))
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
        (fun uu___96_1918  ->
           match uu___96_1918 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____1931 -> None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
        FStar_Range.range) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1952,lb::[]),uu____1954,uu____1955,uu____1956,uu____1957)
          ->
          let uu____1968 =
            let uu____1973 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____1979 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____1973, uu____1979) in
          Some uu____1968
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1986,lbs),uu____1988,uu____1989,uu____1990,uu____1991) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2013 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2020 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2020
                   then
                     let uu____2026 =
                       let uu____2031 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2037 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2031, uu____2037) in
                     Some uu____2026
                   else None)
      | uu____2049 -> None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.term)*
      FStar_Range.range) Prims.option
  =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_new_effect (ne,r) ->
        let uu____2069 =
          let uu____2074 =
            let uu____2077 =
              let uu____2078 =
                let uu____2081 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2081 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2078) in
            inst_tscheme uu____2077 in
          (uu____2074, r) in
        Some uu____2069
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2095,uu____2096,uu____2097,r) ->
        let uu____2103 =
          let uu____2108 =
            let uu____2111 =
              let uu____2112 =
                let uu____2115 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2115 in
              (us, uu____2112) in
            inst_tscheme uu____2111 in
          (uu____2108, r) in
        Some uu____2103
    | uu____2126 -> None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)* FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2161 =
        match uu____2161 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 (FStar_Syntax_Syntax.Sig_datacon
                  (uu____2211,uvs,t,uu____2214,uu____2215,uu____2216,uu____2217,uu____2218),None
                  )
                 ->
                 let uu____2229 =
                   let uu____2234 = inst_tscheme (uvs, t) in
                   (uu____2234, rng) in
                 Some uu____2229
             | FStar_Util.Inr
                 (FStar_Syntax_Syntax.Sig_declare_typ
                  (l,uvs,t,qs,uu____2247),None )
                 ->
                 let uu____2256 =
                   let uu____2257 = in_cur_mod env l in uu____2257 = Yes in
                 if uu____2256
                 then
                   let uu____2263 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2263
                    then
                      let uu____2270 =
                        let uu____2275 = inst_tscheme (uvs, t) in
                        (uu____2275, rng) in
                      Some uu____2270
                    else None)
                 else
                   (let uu____2290 =
                      let uu____2295 = inst_tscheme (uvs, t) in
                      (uu____2295, rng) in
                    Some uu____2290)
             | FStar_Util.Inr
                 (FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid1,uvs,tps,k,uu____2308,uu____2309,uu____2310,uu____2311),None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2331 =
                        let uu____2336 = inst_tscheme (uvs, k) in
                        (uu____2336, rng) in
                      Some uu____2331
                  | uu____2345 ->
                      let uu____2346 =
                        let uu____2351 =
                          let uu____2354 =
                            let uu____2355 =
                              let uu____2358 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2358 in
                            (uvs, uu____2355) in
                          inst_tscheme uu____2354 in
                        (uu____2351, rng) in
                      Some uu____2346)
             | FStar_Util.Inr
                 (FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid1,uvs,tps,k,uu____2373,uu____2374,uu____2375,uu____2376),Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2397 =
                        let uu____2402 = inst_tscheme_with (uvs, k) us in
                        (uu____2402, rng) in
                      Some uu____2397
                  | uu____2411 ->
                      let uu____2412 =
                        let uu____2417 =
                          let uu____2420 =
                            let uu____2421 =
                              let uu____2424 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2424 in
                            (uvs, uu____2421) in
                          inst_tscheme_with uu____2420 us in
                        (uu____2417, rng) in
                      Some uu____2412)
             | FStar_Util.Inr se ->
                 (match se with
                  | (FStar_Syntax_Syntax.Sig_let uu____2449,None ) ->
                      lookup_type_of_let (Prims.fst se) lid
                  | uu____2460 -> effect_signature (Prims.fst se))) in
      let uu____2465 =
        let uu____2471 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2471 mapper in
      match uu____2465 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___110_2523 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___110_2523.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___110_2523.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___110_2523.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2544 = lookup_qname env l in
      match uu____2544 with | None  -> false | Some uu____2564 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ* FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2592 = try_lookup_bv env bv in
      match uu____2592 with
      | None  ->
          let uu____2604 =
            let uu____2605 =
              let uu____2608 = variable_not_found bv in (uu____2608, bvr) in
            FStar_Errors.Error uu____2605 in
          Prims.raise uu____2604
      | Some (t,r) ->
          let uu____2621 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2622 = FStar_Range.set_use_range r bvr in
          (uu____2621, uu____2622)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2634 = try_lookup_lid_aux env l in
      match uu____2634 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2676 =
            let uu____2681 =
              let uu____2684 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2684) in
            (uu____2681, r1) in
          Some uu____2676
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)*
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2701 = try_lookup_lid env l in
      match uu____2701 with
      | None  ->
          let uu____2715 =
            let uu____2716 =
              let uu____2719 = name_not_found l in
              (uu____2719, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2716 in
          Prims.raise uu____2715
      | Some ((us,t),r) -> ((us, t), r)
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___97_2742  ->
              match uu___97_2742 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2744 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme* FStar_Syntax_Syntax.qualifier Prims.list)
        Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2755 = lookup_qname env lid in
      match uu____2755 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_declare_typ
            (uu____2770,uvs,t,q,uu____2774),None ),uu____2775)
          ->
          let uu____2800 =
            let uu____2806 =
              let uu____2809 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2809) in
            (uu____2806, q) in
          Some uu____2800
      | uu____2818 -> None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2840 = lookup_qname env lid in
      match uu____2840 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_declare_typ
            (uu____2853,uvs,t,uu____2856,uu____2857),None ),uu____2858)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2883 ->
          let uu____2894 =
            let uu____2895 =
              let uu____2898 = name_not_found lid in
              (uu____2898, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____2895 in
          Prims.raise uu____2894
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes* FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2909 = lookup_qname env lid in
      match uu____2909 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_datacon
            (uu____2922,uvs,t,uu____2925,uu____2926,uu____2927,uu____2928,uu____2929),None
            ),uu____2930)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2957 ->
          let uu____2968 =
            let uu____2969 =
              let uu____2972 = name_not_found lid in
              (uu____2972, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____2969 in
          Prims.raise uu____2968
let datacons_of_typ:
  env -> FStar_Ident.lident -> (Prims.bool* FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____2984 = lookup_qname env lid in
      match uu____2984 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_inductive_typ
            (uu____2998,uu____2999,uu____3000,uu____3001,uu____3002,dcs,uu____3004,uu____3005),uu____3006),uu____3007)
          -> (true, dcs)
      | uu____3038 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3056 = lookup_qname env lid in
      match uu____3056 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_datacon
            (uu____3067,uu____3068,uu____3069,l,uu____3071,uu____3072,uu____3073,uu____3074),uu____3075),uu____3076)
          -> l
      | uu____3104 ->
          let uu____3115 =
            let uu____3116 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3116 in
          failwith uu____3115
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
        let uu____3140 = lookup_qname env lid in
        match uu____3140 with
        | Some (FStar_Util.Inr (se,None ),uu____3155) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3181,lbs),uu____3183,uu____3184,quals,uu____3186)
                 when visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3203 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3203
                      then
                        let uu____3208 =
                          let uu____3212 =
                            let uu____3213 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3213 in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3212) in
                        Some uu____3208
                      else None)
             | uu____3222 -> None)
        | uu____3225 -> None
let try_lookup_effect_lid:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3246 = lookup_qname env ftv in
      match uu____3246 with
      | Some (FStar_Util.Inr (se,None ),uu____3259) ->
          let uu____3282 = effect_signature se in
          (match uu____3282 with
           | None  -> None
           | Some ((uu____3293,t),r) ->
               let uu____3302 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               Some uu____3302)
      | uu____3303 -> None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3320 = try_lookup_effect_lid env ftv in
      match uu____3320 with
      | None  ->
          let uu____3322 =
            let uu____3323 =
              let uu____3326 = name_not_found ftv in
              (uu____3326, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3323 in
          Prims.raise uu____3322
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
        let uu____3340 = lookup_qname env lid0 in
        match uu____3340 with
        | Some
            (FStar_Util.Inr
             (FStar_Syntax_Syntax.Sig_effect_abbrev
              (lid,univs1,binders,c,quals,uu____3359,uu____3360),None ),uu____3361)
            ->
            let lid1 =
              let uu____3389 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3389 in
            let uu____3390 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___98_3392  ->
                      match uu___98_3392 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3393 -> false)) in
            if uu____3390
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
                     (let uu____3409 =
                        let uu____3410 =
                          FStar_Syntax_Print.lid_to_string lid1 in
                        let uu____3411 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3410 uu____3411 in
                      failwith uu____3409) in
               match (binders, univs1) with
               | ([],uu____3417) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3426,uu____3427::uu____3428::uu____3429) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3432 =
                     let uu____3433 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3434 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3433 uu____3434 in
                   failwith uu____3432
               | uu____3440 ->
                   let uu____3443 =
                     let uu____3446 =
                       let uu____3447 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3447) in
                     inst_tscheme_with uu____3446 insts in
                   (match uu____3443 with
                    | (uu____3455,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3458 =
                          let uu____3459 = FStar_Syntax_Subst.compress t1 in
                          uu____3459.FStar_Syntax_Syntax.n in
                        (match uu____3458 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3489 -> failwith "Impossible")))
        | uu____3493 -> None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3519 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3519 with
        | None  -> None
        | Some (uu____3526,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3531 = find1 l2 in
            (match uu____3531 with | None  -> Some l2 | Some l' -> Some l') in
      let res =
        let uu____3536 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3536 with
        | Some l1 -> l1
        | None  ->
            let uu____3539 = find1 l in
            (match uu____3539 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3551 = lookup_qname env l1 in
      match uu____3551 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____3564),uu____3565),uu____3566)
          -> ne.FStar_Syntax_Syntax.qualifiers
      | uu____3590 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3613 =
          let uu____3614 =
            let uu____3615 = FStar_Util.string_of_int i in
            let uu____3616 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3615 uu____3616 in
          failwith uu____3614 in
        let uu____3617 = lookup_datacon env lid in
        match uu____3617 with
        | (uu____3620,t) ->
            let uu____3622 =
              let uu____3623 = FStar_Syntax_Subst.compress t in
              uu____3623.FStar_Syntax_Syntax.n in
            (match uu____3622 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3627) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3648 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i in
                    FStar_All.pipe_right uu____3648 Prims.fst)
             | uu____3653 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3660 = lookup_qname env l in
      match uu____3660 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_declare_typ
            (uu____3671,uu____3672,uu____3673,quals,uu____3675),uu____3676),uu____3677)
          ->
          FStar_Util.for_some
            (fun uu___99_3703  ->
               match uu___99_3703 with
               | FStar_Syntax_Syntax.Projector uu____3704 -> true
               | uu____3707 -> false) quals
      | uu____3708 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3725 = lookup_qname env lid in
      match uu____3725 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_datacon
            (uu____3736,uu____3737,uu____3738,uu____3739,uu____3740,uu____3741,uu____3742,uu____3743),uu____3744),uu____3745)
          -> true
      | uu____3773 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3790 = lookup_qname env lid in
      match uu____3790 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_inductive_typ
            (uu____3801,uu____3802,uu____3803,uu____3804,uu____3805,uu____3806,tags,uu____3808),uu____3809),uu____3810)
          ->
          FStar_Util.for_some
            (fun uu___100_3840  ->
               match uu___100_3840 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3843 -> false) tags
      | uu____3844 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3861 = lookup_qname env lid in
      match uu____3861 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_let
            (uu____3872,uu____3873,uu____3874,tags,uu____3876),uu____3877),uu____3878)
          ->
          FStar_Util.for_some
            (fun uu___101_3908  ->
               match uu___101_3908 with
               | FStar_Syntax_Syntax.Action uu____3909 -> true
               | uu____3910 -> false) tags
      | uu____3911 -> false
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
      let uu____3930 =
        let uu____3931 = FStar_Syntax_Util.un_uinst head1 in
        uu____3931.FStar_Syntax_Syntax.n in
      match uu____3930 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3935 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____3973 -> Some false
        | FStar_Util.Inr (se,uu____3982) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____3991,uu____3992,uu____3993,qs,uu____3995) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____3998 -> Some true
             | uu____4010 -> Some false) in
      let uu____4011 =
        let uu____4013 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4013 mapper in
      match uu____4011 with | Some b -> b | None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4040 = lookup_qname env lid in
      match uu____4040 with
      | Some
          (FStar_Util.Inr
           (FStar_Syntax_Syntax.Sig_inductive_typ
            (uu____4051,uu____4052,tps,uu____4054,uu____4055,uu____4056,uu____4057,uu____4058),uu____4059),uu____4060)
          -> FStar_List.length tps
      | uu____4093 ->
          let uu____4104 =
            let uu____4105 =
              let uu____4108 = name_not_found lid in
              (uu____4108, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4105 in
          Prims.raise uu____4104
let effect_decl_opt:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4125 = effect_decl_opt env l in
      match uu____4125 with
      | None  ->
          let uu____4127 =
            let uu____4128 =
              let uu____4131 = name_not_found l in
              (uu____4131, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4128 in
          Prims.raise uu____4127
      | Some md -> md
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
            (let uu____4167 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4191  ->
                       match uu____4191 with
                       | (m1,m2,uu____4199,uu____4200,uu____4201) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4167 with
             | None  ->
                 let uu____4210 =
                   let uu____4211 =
                     let uu____4214 =
                       let uu____4215 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4216 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4215
                         uu____4216 in
                     (uu____4214, (env.range)) in
                   FStar_Errors.Error uu____4211 in
                 Prims.raise uu____4210
             | Some (uu____4220,uu____4221,m3,j1,j2) -> (m3, j1, j2))
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
let wp_sig_aux:
  FStar_Syntax_Syntax.eff_decl Prims.list ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____4258 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____4258 with
      | None  ->
          let uu____4267 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____4267
      | Some md ->
          let uu____4273 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____4273 with
           | (uu____4280,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____4288)::(wp,uu____4290)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____4312 -> failwith "Impossible"))
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
                 let uu____4347 = get_range env in
                 let uu____4348 =
                   let uu____4351 =
                     let uu____4352 =
                       let uu____4362 =
                         let uu____4364 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4364] in
                       (null_wp, uu____4362) in
                     FStar_Syntax_Syntax.Tm_app uu____4352 in
                   FStar_Syntax_Syntax.mk uu____4351 in
                 uu____4348 None uu____4347 in
               let uu____4374 =
                 let uu____4375 =
                   let uu____4381 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4381] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4375;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4374)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____4389) ->
          let effects =
            let uu___111_4391 = env.effects in
            {
              decls = (ne :: ((env.effects).decls));
              order = (uu___111_4391.order);
              joins = (uu___111_4391.joins)
            } in
          let uu___112_4392 = env in
          {
            solver = (uu___112_4392.solver);
            range = (uu___112_4392.range);
            curmodule = (uu___112_4392.curmodule);
            gamma = (uu___112_4392.gamma);
            gamma_cache = (uu___112_4392.gamma_cache);
            modules = (uu___112_4392.modules);
            expected_typ = (uu___112_4392.expected_typ);
            sigtab = (uu___112_4392.sigtab);
            is_pattern = (uu___112_4392.is_pattern);
            instantiate_imp = (uu___112_4392.instantiate_imp);
            effects;
            generalize = (uu___112_4392.generalize);
            letrecs = (uu___112_4392.letrecs);
            top_level = (uu___112_4392.top_level);
            check_uvars = (uu___112_4392.check_uvars);
            use_eq = (uu___112_4392.use_eq);
            is_iface = (uu___112_4392.is_iface);
            admit = (uu___112_4392.admit);
            lax = (uu___112_4392.lax);
            lax_universes = (uu___112_4392.lax_universes);
            type_of = (uu___112_4392.type_of);
            universe_of = (uu___112_4392.universe_of);
            use_bv_sorts = (uu___112_4392.use_bv_sorts);
            qname_and_index = (uu___112_4392.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub1,uu____4394) ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4410 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4410 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4489 = (e1.mlift).mlift_wp t wp in
                              let uu____4490 = l1 t wp e in
                              l2 t uu____4489 uu____4490))
                | uu____4491 -> None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4526 = inst_tscheme lift_t in
            match uu____4526 with
            | (uu____4531,lift_t1) ->
                let uu____4533 =
                  let uu____4536 =
                    let uu____4537 =
                      let uu____4547 =
                        let uu____4549 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4550 =
                          let uu____4552 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4552] in
                        uu____4549 :: uu____4550 in
                      (lift_t1, uu____4547) in
                    FStar_Syntax_Syntax.Tm_app uu____4537 in
                  FStar_Syntax_Syntax.mk uu____4536 in
                uu____4533 None wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4597 = inst_tscheme lift_t in
            match uu____4597 with
            | (uu____4602,lift_t1) ->
                let uu____4604 =
                  let uu____4607 =
                    let uu____4608 =
                      let uu____4618 =
                        let uu____4620 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4621 =
                          let uu____4623 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4624 =
                            let uu____4626 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4626] in
                          uu____4623 :: uu____4624 in
                        uu____4620 :: uu____4621 in
                      (lift_t1, uu____4618) in
                    FStar_Syntax_Syntax.Tm_app uu____4608 in
                  FStar_Syntax_Syntax.mk uu____4607 in
                uu____4604 None e.FStar_Syntax_Syntax.pos in
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
              let uu____4667 =
                let uu____4668 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4668
                  FStar_Syntax_Syntax.Delta_constant None in
              FStar_Syntax_Syntax.fv_to_tm uu____4667 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4672 =
              let uu____4673 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4673 in
            let uu____4674 =
              let uu____4675 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4690 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4690) in
              FStar_Util.dflt "none" uu____4675 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4672
              uu____4674 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4708 =
            match uu____4708 with
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
              let uu____4733 =
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
                                    (let uu____4745 =
                                       let uu____4750 =
                                         find_edge order1 (i, k) in
                                       let uu____4752 =
                                         find_edge order1 (k, j) in
                                       (uu____4750, uu____4752) in
                                     match uu____4745 with
                                     | (Some e1,Some e2) ->
                                         let uu____4761 = compose_edges e1 e2 in
                                         [uu____4761]
                                     | uu____4762 -> []))))) in
              FStar_List.append order1 uu____4733 in
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
                   let uu____4777 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4778 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4778
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4777
                   then
                     let uu____4781 =
                       let uu____4782 =
                         let uu____4785 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4786 = get_range env in
                         (uu____4785, uu____4786) in
                       FStar_Errors.Error uu____4782 in
                     Prims.raise uu____4781
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
                                            let uu____4849 =
                                              let uu____4854 =
                                                find_edge order2 (i, k) in
                                              let uu____4856 =
                                                find_edge order2 (j, k) in
                                              (uu____4854, uu____4856) in
                                            match uu____4849 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____4879,uu____4880)
                                                     ->
                                                     let uu____4884 =
                                                       let uu____4887 =
                                                         let uu____4888 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____4888 in
                                                       let uu____4890 =
                                                         let uu____4891 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____4891 in
                                                       (uu____4887,
                                                         uu____4890) in
                                                     (match uu____4884 with
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
                                            | uu____4910 -> bopt) None) in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___113_4949 = env.effects in
              { decls = (uu___113_4949.decls); order = order2; joins } in
            let uu___114_4950 = env in
            {
              solver = (uu___114_4950.solver);
              range = (uu___114_4950.range);
              curmodule = (uu___114_4950.curmodule);
              gamma = (uu___114_4950.gamma);
              gamma_cache = (uu___114_4950.gamma_cache);
              modules = (uu___114_4950.modules);
              expected_typ = (uu___114_4950.expected_typ);
              sigtab = (uu___114_4950.sigtab);
              is_pattern = (uu___114_4950.is_pattern);
              instantiate_imp = (uu___114_4950.instantiate_imp);
              effects;
              generalize = (uu___114_4950.generalize);
              letrecs = (uu___114_4950.letrecs);
              top_level = (uu___114_4950.top_level);
              check_uvars = (uu___114_4950.check_uvars);
              use_eq = (uu___114_4950.use_eq);
              is_iface = (uu___114_4950.is_iface);
              admit = (uu___114_4950.admit);
              lax = (uu___114_4950.lax);
              lax_universes = (uu___114_4950.lax_universes);
              type_of = (uu___114_4950.type_of);
              universe_of = (uu___114_4950.universe_of);
              use_bv_sorts = (uu___114_4950.use_bv_sorts);
              qname_and_index = (uu___114_4950.qname_and_index)
            }))
      | uu____4951 -> env
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
        | uu____4973 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____4981 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____4981 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____4991 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____4991 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5008 =
                     let uu____5009 =
                       let uu____5012 =
                         let uu____5013 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5019 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5027 =
                           let uu____5028 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5028 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5013 uu____5019 uu____5027 in
                       (uu____5012, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5009 in
                   Prims.raise uu____5008)
                else ();
                (let inst1 =
                   let uu____5032 =
                     let uu____5038 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5038 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5045  ->
                        fun uu____5046  ->
                          match (uu____5045, uu____5046) with
                          | ((x,uu____5060),(t,uu____5062)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5032 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5077 =
                     let uu___115_5078 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___115_5078.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___115_5078.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___115_5078.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___115_5078.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5077
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5108 =
    let uu____5110 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5110 in
  match uu____5108 with
  | None  -> None
  | Some ed ->
      let uu____5117 =
        only_reifiable &&
          (let uu____5118 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5118) in
      if uu____5117
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5131 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5133 =
               let uu____5142 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5142) in
             (match uu____5133 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5176 =
                    let uu____5179 = get_range env in
                    let uu____5180 =
                      let uu____5183 =
                        let uu____5184 =
                          let uu____5194 =
                            let uu____5196 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5196; wp] in
                          (repr, uu____5194) in
                        FStar_Syntax_Syntax.Tm_app uu____5184 in
                      FStar_Syntax_Syntax.mk uu____5183 in
                    uu____5180 None uu____5179 in
                  Some uu____5176))
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
          let uu____5240 =
            let uu____5241 =
              let uu____5244 =
                let uu____5245 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5245 in
              let uu____5246 = get_range env in (uu____5244, uu____5246) in
            FStar_Errors.Error uu____5241 in
          Prims.raise uu____5240 in
        let uu____5247 = effect_repr_aux true env c u_c in
        match uu____5247 with
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
        | FStar_Util.Inr (eff_name,uu____5279) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5292 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5299 =
        let uu____5300 = FStar_Syntax_Subst.compress t in
        uu____5300.FStar_Syntax_Syntax.n in
      match uu____5299 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5303,c) ->
          is_reifiable_comp env c
      | uu____5315 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5340 = push1 x rest1 in local :: uu____5340 in
      let uu___116_5342 = env in
      let uu____5343 = push1 s env.gamma in
      {
        solver = (uu___116_5342.solver);
        range = (uu___116_5342.range);
        curmodule = (uu___116_5342.curmodule);
        gamma = uu____5343;
        gamma_cache = (uu___116_5342.gamma_cache);
        modules = (uu___116_5342.modules);
        expected_typ = (uu___116_5342.expected_typ);
        sigtab = (uu___116_5342.sigtab);
        is_pattern = (uu___116_5342.is_pattern);
        instantiate_imp = (uu___116_5342.instantiate_imp);
        effects = (uu___116_5342.effects);
        generalize = (uu___116_5342.generalize);
        letrecs = (uu___116_5342.letrecs);
        top_level = (uu___116_5342.top_level);
        check_uvars = (uu___116_5342.check_uvars);
        use_eq = (uu___116_5342.use_eq);
        is_iface = (uu___116_5342.is_iface);
        admit = (uu___116_5342.admit);
        lax = (uu___116_5342.lax);
        lax_universes = (uu___116_5342.lax_universes);
        type_of = (uu___116_5342.type_of);
        universe_of = (uu___116_5342.universe_of);
        use_bv_sorts = (uu___116_5342.use_bv_sorts);
        qname_and_index = (uu___116_5342.qname_and_index)
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
      let uu___117_5370 = env in
      {
        solver = (uu___117_5370.solver);
        range = (uu___117_5370.range);
        curmodule = (uu___117_5370.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___117_5370.gamma_cache);
        modules = (uu___117_5370.modules);
        expected_typ = (uu___117_5370.expected_typ);
        sigtab = (uu___117_5370.sigtab);
        is_pattern = (uu___117_5370.is_pattern);
        instantiate_imp = (uu___117_5370.instantiate_imp);
        effects = (uu___117_5370.effects);
        generalize = (uu___117_5370.generalize);
        letrecs = (uu___117_5370.letrecs);
        top_level = (uu___117_5370.top_level);
        check_uvars = (uu___117_5370.check_uvars);
        use_eq = (uu___117_5370.use_eq);
        is_iface = (uu___117_5370.is_iface);
        admit = (uu___117_5370.admit);
        lax = (uu___117_5370.lax);
        lax_universes = (uu___117_5370.lax_universes);
        type_of = (uu___117_5370.type_of);
        universe_of = (uu___117_5370.universe_of);
        use_bv_sorts = (uu___117_5370.use_bv_sorts);
        qname_and_index = (uu___117_5370.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5386  ->
             match uu____5386 with | (x,uu____5390) -> push_bv env1 x) env bs
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
            let uu___118_5410 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___118_5410.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___118_5410.FStar_Syntax_Syntax.index);
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
      (let uu___119_5440 = env in
       {
         solver = (uu___119_5440.solver);
         range = (uu___119_5440.range);
         curmodule = (uu___119_5440.curmodule);
         gamma = [];
         gamma_cache = (uu___119_5440.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___119_5440.sigtab);
         is_pattern = (uu___119_5440.is_pattern);
         instantiate_imp = (uu___119_5440.instantiate_imp);
         effects = (uu___119_5440.effects);
         generalize = (uu___119_5440.generalize);
         letrecs = (uu___119_5440.letrecs);
         top_level = (uu___119_5440.top_level);
         check_uvars = (uu___119_5440.check_uvars);
         use_eq = (uu___119_5440.use_eq);
         is_iface = (uu___119_5440.is_iface);
         admit = (uu___119_5440.admit);
         lax = (uu___119_5440.lax);
         lax_universes = (uu___119_5440.lax_universes);
         type_of = (uu___119_5440.type_of);
         universe_of = (uu___119_5440.universe_of);
         use_bv_sorts = (uu___119_5440.use_bv_sorts);
         qname_and_index = (uu___119_5440.qname_and_index)
       })
let push_univ_vars: env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___120_5455 = env in
      {
        solver = (uu___120_5455.solver);
        range = (uu___120_5455.range);
        curmodule = (uu___120_5455.curmodule);
        gamma = (uu___120_5455.gamma);
        gamma_cache = (uu___120_5455.gamma_cache);
        modules = (uu___120_5455.modules);
        expected_typ = (Some t);
        sigtab = (uu___120_5455.sigtab);
        is_pattern = (uu___120_5455.is_pattern);
        instantiate_imp = (uu___120_5455.instantiate_imp);
        effects = (uu___120_5455.effects);
        generalize = (uu___120_5455.generalize);
        letrecs = (uu___120_5455.letrecs);
        top_level = (uu___120_5455.top_level);
        check_uvars = (uu___120_5455.check_uvars);
        use_eq = false;
        is_iface = (uu___120_5455.is_iface);
        admit = (uu___120_5455.admit);
        lax = (uu___120_5455.lax);
        lax_universes = (uu___120_5455.lax_universes);
        type_of = (uu___120_5455.type_of);
        universe_of = (uu___120_5455.universe_of);
        use_bv_sorts = (uu___120_5455.use_bv_sorts);
        qname_and_index = (uu___120_5455.qname_and_index)
      }
let expected_typ: env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t
let clear_expected_typ: env -> (env* FStar_Syntax_Syntax.typ Prims.option) =
  fun env_  ->
    let uu____5471 = expected_typ env_ in
    ((let uu___121_5474 = env_ in
      {
        solver = (uu___121_5474.solver);
        range = (uu___121_5474.range);
        curmodule = (uu___121_5474.curmodule);
        gamma = (uu___121_5474.gamma);
        gamma_cache = (uu___121_5474.gamma_cache);
        modules = (uu___121_5474.modules);
        expected_typ = None;
        sigtab = (uu___121_5474.sigtab);
        is_pattern = (uu___121_5474.is_pattern);
        instantiate_imp = (uu___121_5474.instantiate_imp);
        effects = (uu___121_5474.effects);
        generalize = (uu___121_5474.generalize);
        letrecs = (uu___121_5474.letrecs);
        top_level = (uu___121_5474.top_level);
        check_uvars = (uu___121_5474.check_uvars);
        use_eq = false;
        is_iface = (uu___121_5474.is_iface);
        admit = (uu___121_5474.admit);
        lax = (uu___121_5474.lax);
        lax_universes = (uu___121_5474.lax_universes);
        type_of = (uu___121_5474.type_of);
        universe_of = (uu___121_5474.universe_of);
        use_bv_sorts = (uu___121_5474.use_bv_sorts);
        qname_and_index = (uu___121_5474.qname_and_index)
      }), uu____5471)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5485 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___102_5489  ->
                    match uu___102_5489 with
                    | Binding_sig (uu____5491,se) -> [se]
                    | uu____5495 -> [])) in
          FStar_All.pipe_right uu____5485 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___122_5500 = env in
       {
         solver = (uu___122_5500.solver);
         range = (uu___122_5500.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___122_5500.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___122_5500.expected_typ);
         sigtab = (uu___122_5500.sigtab);
         is_pattern = (uu___122_5500.is_pattern);
         instantiate_imp = (uu___122_5500.instantiate_imp);
         effects = (uu___122_5500.effects);
         generalize = (uu___122_5500.generalize);
         letrecs = (uu___122_5500.letrecs);
         top_level = (uu___122_5500.top_level);
         check_uvars = (uu___122_5500.check_uvars);
         use_eq = (uu___122_5500.use_eq);
         is_iface = (uu___122_5500.is_iface);
         admit = (uu___122_5500.admit);
         lax = (uu___122_5500.lax);
         lax_universes = (uu___122_5500.lax_universes);
         type_of = (uu___122_5500.type_of);
         universe_of = (uu___122_5500.universe_of);
         use_bv_sorts = (uu___122_5500.use_bv_sorts);
         qname_and_index = (uu___122_5500.qname_and_index)
       })
let uvars_in_env:
  env -> (FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ) FStar_Util.set =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5550)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5565 =
            let uu____5569 = FStar_Syntax_Free.uvars t in ext out uu____5569 in
          aux uu____5565 tl1
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
          let uu____5625 =
            let uu____5627 = FStar_Syntax_Free.univs t in ext out uu____5627 in
          aux uu____5625 tl1
      | (Binding_sig uu____5629)::uu____5630 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5667)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5677 = FStar_Util.set_add uname out in aux uu____5677 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5691 =
            let uu____5693 = FStar_Syntax_Free.univnames t in
            ext out uu____5693 in
          aux uu____5691 tl1
      | (Binding_sig uu____5695)::uu____5696 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___103_5712  ->
            match uu___103_5712 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5724 =
      let uu____5726 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____5726
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____5724 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___104_5777  ->
             match uu___104_5777 with
             | Binding_sig (lids,uu____5781) -> FStar_List.append lids keys
             | uu____5784 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____5786  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____5790  -> ());
    push = (fun uu____5791  -> ());
    pop = (fun uu____5792  -> ());
    mark = (fun uu____5793  -> ());
    reset_mark = (fun uu____5794  -> ());
    commit_mark = (fun uu____5795  -> ());
    encode_modul = (fun uu____5796  -> fun uu____5797  -> ());
    encode_sig = (fun uu____5798  -> fun uu____5799  -> ());
    solve = (fun uu____5800  -> fun uu____5801  -> fun uu____5802  -> ());
    is_trivial = (fun uu____5806  -> fun uu____5807  -> false);
    finish = (fun uu____5808  -> ());
    refresh = (fun uu____5809  -> ())
  }