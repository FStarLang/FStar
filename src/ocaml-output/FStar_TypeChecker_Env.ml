open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv 
  | Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) 
  | Binding_sig of (FStar_Ident.lident Prims.list *
  FStar_Syntax_Syntax.sigelt) 
  | Binding_univ of FStar_Syntax_Syntax.univ_name 
  | Binding_sig_inst of (FStar_Ident.lident Prims.list *
  FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____29 -> false
  
let __proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_lid : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____43 -> false
  
let __proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let uu___is_Binding_sig : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____64 -> false
  
let __proj__Binding_sig__item___0 :
  binding -> (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let uu___is_Binding_univ : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____85 -> false
  
let __proj__Binding_univ__item___0 : binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let uu___is_Binding_sig_inst : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____101 -> false
  
let __proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt *
      FStar_Syntax_Syntax.universes)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0 
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let uu___is_NoDelta : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____127 -> false
  
let uu___is_Inlining : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____131 -> false
  
let uu___is_Eager_unfolding_only : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____135 -> false
  
let uu___is_Unfold : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____140 -> false
  
let __proj__Unfold__item___0 : delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0 
type normal_comp_typ =
  {
  nct_name: FStar_Ident.lident ;
  nct_univs: FStar_Syntax_Syntax.universes ;
  nct_indices: FStar_Syntax_Syntax.args ;
  nct_result: FStar_Syntax_Syntax.arg ;
  nct_wp: FStar_Syntax_Syntax.arg ;
  nct_flags: FStar_Syntax_Syntax.cflags Prims.list }
type nct = normal_comp_typ
type mlift = normal_comp_typ -> normal_comp_typ
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
type effects =
  {
  decls: FStar_Syntax_Syntax.eff_decl Prims.list ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    }
type cached_elt =
  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                               *
                                                               FStar_Syntax_Syntax.universes
                                                               Prims.option))
    FStar_Util.either
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ Prims.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  is_pattern: Prims.bool ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs: (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  use_bv_sorts: Prims.bool ;
  qname_and_index: (FStar_Ident.lident * Prims.int) Prims.option }
and solver_t =
  {
  init: env -> Prims.unit ;
  push: Prims.string -> Prims.unit ;
  pop: Prims.string -> Prims.unit ;
  mark: Prims.string -> Prims.unit ;
  reset_mark: Prims.string -> Prims.unit ;
  commit_mark: Prims.string -> Prims.unit ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit ;
  solve:
    (Prims.unit -> Prims.string) Prims.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
    ;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool ;
  finish: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit }
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list)
    ;
  implicits:
    (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term
      * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
    }
type implicits =
  (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term *
    FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify : env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,_)
        |(Eager_unfolding_only
          ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
         |(Unfold _,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          |(Unfold _,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____805 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____815 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____823 =
  FStar_Util.smap_create (Prims.parse_int "100") 
let initial_env :
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____862 = new_gamma_cache ()  in
          let uu____864 = new_sigtab ()  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____862;
            modules = [];
            expected_typ = None;
            sigtab = uu____864;
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
  
let sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab 
let gamma_cache : env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache 
let query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let push_query_indices : Prims.unit -> Prims.unit =
  fun uu____904  ->
    let uu____905 = FStar_ST.read query_indices  in
    match uu____905 with
    | [] -> failwith "Empty query indices!"
    | uu____919 ->
        let uu____924 =
          let uu____929 =
            let uu____933 = FStar_ST.read query_indices  in
            FStar_List.hd uu____933  in
          let uu____947 = FStar_ST.read query_indices  in uu____929 ::
            uu____947
           in
        FStar_ST.write query_indices uu____924
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____969  ->
    let uu____970 = FStar_ST.read query_indices  in
    match uu____970 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____1006  ->
    match uu____1006 with
    | (l,n1) ->
        let uu____1011 = FStar_ST.read query_indices  in
        (match uu____1011 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1045 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1055  ->
    let uu____1056 = FStar_ST.read query_indices  in FStar_List.hd uu____1056
  
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1072  ->
    let uu____1073 = FStar_ST.read query_indices  in
    match uu____1073 with
    | hd1::uu____1085::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1112 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____1126 =
       let uu____1128 = FStar_ST.read stack  in env :: uu____1128  in
     FStar_ST.write stack uu____1126);
    (let uu___109_1136 = env  in
     let uu____1137 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____1139 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___109_1136.solver);
       range = (uu___109_1136.range);
       curmodule = (uu___109_1136.curmodule);
       gamma = (uu___109_1136.gamma);
       gamma_cache = uu____1137;
       modules = (uu___109_1136.modules);
       expected_typ = (uu___109_1136.expected_typ);
       sigtab = uu____1139;
       is_pattern = (uu___109_1136.is_pattern);
       instantiate_imp = (uu___109_1136.instantiate_imp);
       effects = (uu___109_1136.effects);
       generalize = (uu___109_1136.generalize);
       letrecs = (uu___109_1136.letrecs);
       top_level = (uu___109_1136.top_level);
       check_uvars = (uu___109_1136.check_uvars);
       use_eq = (uu___109_1136.use_eq);
       is_iface = (uu___109_1136.is_iface);
       admit = (uu___109_1136.admit);
       lax = (uu___109_1136.lax);
       lax_universes = (uu___109_1136.lax_universes);
       type_of = (uu___109_1136.type_of);
       universe_of = (uu___109_1136.universe_of);
       use_bv_sorts = (uu___109_1136.use_bv_sorts);
       qname_and_index = (uu___109_1136.qname_and_index)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1143  ->
    let uu____1144 = FStar_ST.read stack  in
    match uu____1144 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1156 -> failwith "Impossible: Too many pops"
  
let cleanup_interactive : env -> Prims.unit = fun env  -> (env.solver).pop "" 
let push : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
  
let pop : env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
  
let mark : env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
  
let commit_mark : env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____1188 = pop_stack ()  in ());
    env
  
let reset_mark : env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
  
let incr_query_index : env -> env =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qname_and_index with
    | None  -> env
    | Some (l,n1) ->
        let uu____1207 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1219  ->
                  match uu____1219 with
                  | (m,uu____1223) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1207 with
         | None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___110_1228 = env  in
               {
                 solver = (uu___110_1228.solver);
                 range = (uu___110_1228.range);
                 curmodule = (uu___110_1228.curmodule);
                 gamma = (uu___110_1228.gamma);
                 gamma_cache = (uu___110_1228.gamma_cache);
                 modules = (uu___110_1228.modules);
                 expected_typ = (uu___110_1228.expected_typ);
                 sigtab = (uu___110_1228.sigtab);
                 is_pattern = (uu___110_1228.is_pattern);
                 instantiate_imp = (uu___110_1228.instantiate_imp);
                 effects = (uu___110_1228.effects);
                 generalize = (uu___110_1228.generalize);
                 letrecs = (uu___110_1228.letrecs);
                 top_level = (uu___110_1228.top_level);
                 check_uvars = (uu___110_1228.check_uvars);
                 use_eq = (uu___110_1228.use_eq);
                 is_iface = (uu___110_1228.is_iface);
                 admit = (uu___110_1228.admit);
                 lax = (uu___110_1228.lax);
                 lax_universes = (uu___110_1228.lax_universes);
                 type_of = (uu___110_1228.type_of);
                 universe_of = (uu___110_1228.universe_of);
                 use_bv_sorts = (uu___110_1228.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1231,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___111_1237 = env  in
               {
                 solver = (uu___111_1237.solver);
                 range = (uu___111_1237.range);
                 curmodule = (uu___111_1237.curmodule);
                 gamma = (uu___111_1237.gamma);
                 gamma_cache = (uu___111_1237.gamma_cache);
                 modules = (uu___111_1237.modules);
                 expected_typ = (uu___111_1237.expected_typ);
                 sigtab = (uu___111_1237.sigtab);
                 is_pattern = (uu___111_1237.is_pattern);
                 instantiate_imp = (uu___111_1237.instantiate_imp);
                 effects = (uu___111_1237.effects);
                 generalize = (uu___111_1237.generalize);
                 letrecs = (uu___111_1237.letrecs);
                 top_level = (uu___111_1237.top_level);
                 check_uvars = (uu___111_1237.check_uvars);
                 use_eq = (uu___111_1237.use_eq);
                 is_iface = (uu___111_1237.is_iface);
                 admit = (uu___111_1237.admit);
                 lax = (uu___111_1237.lax);
                 lax_universes = (uu___111_1237.lax_universes);
                 type_of = (uu___111_1237.type_of);
                 universe_of = (uu___111_1237.universe_of);
                 use_bv_sorts = (uu___111_1237.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               })))
  
let debug : env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let set_range : env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___112_1253 = e  in
         {
           solver = (uu___112_1253.solver);
           range = r;
           curmodule = (uu___112_1253.curmodule);
           gamma = (uu___112_1253.gamma);
           gamma_cache = (uu___112_1253.gamma_cache);
           modules = (uu___112_1253.modules);
           expected_typ = (uu___112_1253.expected_typ);
           sigtab = (uu___112_1253.sigtab);
           is_pattern = (uu___112_1253.is_pattern);
           instantiate_imp = (uu___112_1253.instantiate_imp);
           effects = (uu___112_1253.effects);
           generalize = (uu___112_1253.generalize);
           letrecs = (uu___112_1253.letrecs);
           top_level = (uu___112_1253.top_level);
           check_uvars = (uu___112_1253.check_uvars);
           use_eq = (uu___112_1253.use_eq);
           is_iface = (uu___112_1253.is_iface);
           admit = (uu___112_1253.admit);
           lax = (uu___112_1253.lax);
           lax_universes = (uu___112_1253.lax_universes);
           type_of = (uu___112_1253.type_of);
           universe_of = (uu___112_1253.universe_of);
           use_bv_sorts = (uu___112_1253.use_bv_sorts);
           qname_and_index = (uu___112_1253.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___113_1270 = env  in
      {
        solver = (uu___113_1270.solver);
        range = (uu___113_1270.range);
        curmodule = lid;
        gamma = (uu___113_1270.gamma);
        gamma_cache = (uu___113_1270.gamma_cache);
        modules = (uu___113_1270.modules);
        expected_typ = (uu___113_1270.expected_typ);
        sigtab = (uu___113_1270.sigtab);
        is_pattern = (uu___113_1270.is_pattern);
        instantiate_imp = (uu___113_1270.instantiate_imp);
        effects = (uu___113_1270.effects);
        generalize = (uu___113_1270.generalize);
        letrecs = (uu___113_1270.letrecs);
        top_level = (uu___113_1270.top_level);
        check_uvars = (uu___113_1270.check_uvars);
        use_eq = (uu___113_1270.use_eq);
        is_iface = (uu___113_1270.is_iface);
        admit = (uu___113_1270.admit);
        lax = (uu___113_1270.lax);
        lax_universes = (uu___113_1270.lax_universes);
        type_of = (uu___113_1270.type_of);
        universe_of = (uu___113_1270.universe_of);
        use_bv_sorts = (uu___113_1270.use_bv_sorts);
        qname_and_index = (uu___113_1270.qname_and_index)
      }
  
let has_interface : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let find_in_sigtab :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt Prims.option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
  
let name_not_found : Prims.string -> FStar_Ident.lid -> Prims.string =
  fun origin  ->
    fun l  ->
      FStar_Util.format2 "Name \"%s\" not found (from %s)" l.FStar_Ident.str
        origin
  
let variable_not_found : FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1295 = FStar_Syntax_Print.bv_to_string v1  in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1295
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1298  ->
    let uu____1299 = FStar_Unionfind.fresh None  in
    FStar_Syntax_Syntax.U_unif uu____1299
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.term
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> t
      | ((formals,t),uu____1317) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          FStar_Syntax_Subst.subst vs t
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universe Prims.list * FStar_Syntax_Syntax.term)
  =
  fun uu___95_1337  ->
    match uu___95_1337 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1351  -> new_u_univ ()))
           in
        let uu____1352 = inst_tscheme_with (us, t) us'  in (us', uu____1352)
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1363 = inst_tscheme t  in
      match uu____1363 with
      | (us,t1) ->
          let uu____1370 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____1370)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1382  ->
          match uu____1382 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1396 =
                         let uu____1397 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____1400 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____1403 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____1404 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1397 uu____1400 uu____1403 uu____1404
                          in
                       failwith uu____1396)
                    else ();
                    inst_tscheme_with
                      ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                        t) insts)
               | uu____1407 ->
                   let uu____1408 =
                     let uu____1409 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1409
                      in
                   failwith uu____1408)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1413 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1417 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1421 -> false
  
let in_cur_mod : env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____1447) -> Maybe
             | (uu____1451,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1463 -> No  in
           aux cur1 lns)
        else No
  
let lookup_qname :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                   *
                                                                   FStar_Syntax_Syntax.universes
                                                                   Prims.option))
        FStar_Util.either Prims.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t; Some t
         in
      let found =
        if cur_mod <> No
        then
          let uu____1515 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1515 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___96_1532  ->
                   match uu___96_1532 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1551 =
                           let uu____1559 = inst_tscheme t  in
                           FStar_Util.Inl uu____1559  in
                         Some uu____1551
                       else None
                   | Binding_sig
                       (uu____1582,FStar_Syntax_Syntax.Sig_bundle
                        (ses,uu____1584,uu____1585,uu____1586))
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1596 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1596
                            then cache (FStar_Util.Inr (se, None))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1616 ->
                             Some t
                         | uu____1623 -> cache t  in
                       let uu____1624 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1624
                       then maybe_cache (FStar_Util.Inr (s, None))
                       else None
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1653 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1653
                       then Some (FStar_Util.Inr (s, (Some us)))
                       else None
                   | uu____1684 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1718 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____1718
         then
           let uu____1727 = find_in_sigtab env lid  in
           match uu____1727 with
           | Some se -> Some (FStar_Util.Inr (se, None))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1778,uu____1779,uu____1780)
          -> add_sigelts env ses
      | uu____1787 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se with
            | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1793) ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____1797 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____1851)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____1866 =
            let uu____1870 = FStar_Syntax_Free.uvars t  in ext out uu____1870
             in
          aux uu____1866 tl1
      | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> out  in
    aux no_uvs1 env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst _)::tl1|(Binding_univ _)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____1926 =
            let uu____1928 = FStar_Syntax_Free.univs t  in ext out uu____1928
             in
          aux uu____1926 tl1
      | (Binding_sig uu____1930)::uu____1931 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____1968)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____1978 = FStar_Util.set_add uname out  in
          aux uu____1978 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____1992 =
            let uu____1994 = FStar_Syntax_Free.univnames t  in
            ext out uu____1994  in
          aux uu____1992 tl1
      | (Binding_sig uu____1996)::uu____1997 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___97_2013  ->
            match uu___97_2013 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____2025 =
      let uu____2027 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____2027
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____2025 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let t_binders :
  env -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list =
  fun env  ->
    let uu____2043 = all_binders env  in
    FStar_All.pipe_right uu____2043
      (FStar_List.filter
         (fun uu____2049  ->
            match uu____2049 with
            | (x,uu____2053) ->
                let uu____2054 =
                  let uu____2055 =
                    FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort
                     in
                  uu____2055.FStar_Syntax_Syntax.n  in
                (match uu____2054 with
                 | FStar_Syntax_Syntax.Tm_type uu____2058 -> true
                 | uu____2059 -> false)))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___98_2098  ->
             match uu___98_2098 with
             | Binding_sig (lids,uu____2102) -> FStar_List.append lids keys
             | uu____2105 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____2107  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___99_2122  ->
           match uu___99_2122 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some (id.FStar_Syntax_Syntax.sort)
           | uu____2129 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2144,lb::[]),uu____2146,uu____2147,uu____2148,uu____2149)
          ->
          let uu____2160 =
            inst_tscheme
              ((lb.FStar_Syntax_Syntax.lbunivs),
                (lb.FStar_Syntax_Syntax.lbtyp))
             in
          Some uu____2160
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2168,lbs),uu____2170,uu____2171,uu____2172,uu____2173) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2191 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2196 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____2196
                   then
                     let uu____2200 =
                       inst_tscheme
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp))
                        in
                     Some uu____2200
                   else None)
      | uu____2211 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____2224) ->
        let uu____2225 =
          let uu____2228 =
            let uu____2229 =
              FStar_Syntax_Util.maybe_tot_arrow
                ne.FStar_Syntax_Syntax.binders
                ne.FStar_Syntax_Syntax.signature
               in
            ((ne.FStar_Syntax_Syntax.univs), uu____2229)  in
          inst_tscheme uu____2228  in
        Some uu____2225
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2235,uu____2236,uu____2237,uu____2238) ->
        let uu____2243 =
          let uu____2246 =
            let uu____2247 =
              FStar_Syntax_Util.maybe_tot_arrow binders
                FStar_Syntax_Syntax.teff
               in
            (us, uu____2247)  in
          inst_tscheme uu____2246  in
        Some uu____2243
    | uu____2250 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu___100_2277 =
        match uu___100_2277 with
        | FStar_Util.Inl t -> Some t
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_datacon
             (uu____2298,uvs,t,uu____2301,uu____2302,uu____2303,uu____2304,uu____2305),None
             )
            -> let uu____2316 = inst_tscheme (uvs, t)  in Some uu____2316
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t,qs,uu____2325),None
             )
            ->
            let uu____2334 =
              let uu____2335 = in_cur_mod env l  in uu____2335 = Yes  in
            if uu____2334
            then
              let uu____2339 =
                (FStar_All.pipe_right qs
                   (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                  || env.is_iface
                 in
              (if uu____2339
               then
                 let uu____2344 = inst_tscheme (uvs, t)  in Some uu____2344
               else None)
            else (let uu____2353 = inst_tscheme (uvs, t)  in Some uu____2353)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid1,uvs,tps,k,uu____2362,uu____2363,uu____2364,uu____2365),None
             )
            ->
            (match tps with
             | [] ->
                 let uu____2383 = inst_tscheme (uvs, k)  in
                 FStar_All.pipe_left (fun _0_28  -> Some _0_28) uu____2383
             | uu____2393 ->
                 let uu____2394 =
                   let uu____2397 =
                     let uu____2398 =
                       let uu____2401 = FStar_Syntax_Syntax.mk_Total k  in
                       FStar_Syntax_Util.flat_arrow tps uu____2401  in
                     (uvs, uu____2398)  in
                   inst_tscheme uu____2397  in
                 FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____2394)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid1,uvs,tps,k,uu____2415,uu____2416,uu____2417,uu____2418),Some
             us)
            ->
            (match tps with
             | [] ->
                 let uu____2437 =
                   let uu____2440 = inst_tscheme_with (uvs, k) us  in
                   (us, uu____2440)  in
                 FStar_All.pipe_left (fun _0_30  -> Some _0_30) uu____2437
             | uu____2448 ->
                 let uu____2449 =
                   let uu____2452 =
                     let uu____2453 =
                       let uu____2454 =
                         let uu____2457 = FStar_Syntax_Syntax.mk_Total k  in
                         FStar_Syntax_Util.flat_arrow tps uu____2457  in
                       (uvs, uu____2454)  in
                     inst_tscheme_with uu____2453 us  in
                   (us, uu____2452)  in
                 FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____2449)
        | FStar_Util.Inr se ->
            (match se with
             | (FStar_Syntax_Syntax.Sig_let uu____2479,None ) ->
                 lookup_type_of_let (Prims.fst se) lid
             | uu____2490 -> effect_signature (Prims.fst se))
         in
      let uu____2495 =
        let uu____2499 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____2499 mapper  in
      match uu____2495 with
      | Some (us,t) ->
          Some
            (us,
              (let uu___114_2532 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_2532.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.tk =
                   (uu___114_2532.FStar_Syntax_Syntax.tk);
                 FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_2532.FStar_Syntax_Syntax.vars)
               }))
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2549 = lookup_qname env l  in
      match uu____2549 with | None  -> false | Some uu____2565 -> true
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun bv  ->
      let uu____2586 = try_lookup_bv env bv  in
      match uu____2586 with
      | None  ->
          let uu____2592 =
            let uu____2593 =
              let uu____2596 = variable_not_found bv  in
              let uu____2597 = FStar_Syntax_Syntax.range_of_bv bv  in
              (uu____2596, uu____2597)  in
            FStar_Errors.Error uu____2593  in
          Prims.raise uu____2592
      | Some t ->
          let uu____2603 = FStar_Syntax_Syntax.range_of_bv bv  in
          FStar_Syntax_Subst.set_use_range uu____2603 t
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2613 = try_lookup_lid_aux env l  in
      match uu____2613 with
      | None  -> None
      | Some (us,t) ->
          let uu____2638 =
            let uu____2641 =
              FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t
               in
            (us, uu____2641)  in
          Some uu____2638
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun l  ->
      let uu____2652 = try_lookup_lid env l  in
      match uu____2652 with
      | None  ->
          let uu____2660 =
            let uu____2661 =
              let uu____2664 = name_not_found "lookup_lid" l  in
              (uu____2664, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____2661  in
          Prims.raise uu____2660
      | Some (us,t) -> (us, t)
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_2678  ->
              match uu___101_2678 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2680 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2691 = lookup_qname env lid  in
      match uu____2691 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2704,uvs,t,q,uu____2708),None ))
          ->
          let uu____2724 =
            let uu____2730 =
              let uu____2733 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____2733)  in
            (uu____2730, q)  in
          Some uu____2724
      | uu____2742 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2762 = lookup_qname env lid  in
      match uu____2762 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2773,uvs,t,uu____2776,uu____2777),None ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2793 ->
          let uu____2802 =
            let uu____2803 =
              let uu____2806 = name_not_found "lookup_val_decl" lid  in
              (uu____2806, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2803  in
          Prims.raise uu____2802
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2817 = lookup_qname env lid  in
      match uu____2817 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2828,uvs,t,uu____2831,uu____2832,uu____2833,uu____2834,uu____2835),None
           ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2853 ->
          let uu____2862 =
            let uu____2863 =
              let uu____2866 = name_not_found "lookup_datacon" lid  in
              (uu____2866, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2863  in
          Prims.raise uu____2862
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____2878 = lookup_qname env lid  in
      match uu____2878 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2890,uu____2891,uu____2892,uu____2893,uu____2894,dcs,uu____2896,uu____2897),uu____2898))
          -> (true, dcs)
      | uu____2920 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____2936 = lookup_qname env lid  in
      match uu____2936 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2945,uu____2946,uu____2947,l,uu____2949,uu____2950,uu____2951,uu____2952),uu____2953))
          -> l
      | uu____2972 ->
          let uu____2981 =
            let uu____2982 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____2982  in
          failwith uu____2981
  
let lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
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
                    (FStar_Util.for_some (visible_at dl))))
           in
        let uu____3006 = lookup_qname env lid  in
        match uu____3006 with
        | Some (FStar_Util.Inr (se,None )) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3035,lbs),uu____3037,uu____3038,quals,uu____3040)
                 when visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____3057 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____3057
                      then
                        let uu____3062 =
                          let uu____3066 =
                            let uu____3067 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef
                               in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3067
                             in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3066)  in
                        Some uu____3062
                      else None)
             | uu____3076 -> None)
        | uu____3079 -> None
  
let try_lookup_effect_lid' :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option
  =
  fun env  ->
    fun ftv  ->
      let uu____3102 = lookup_qname env ftv  in
      match uu____3102 with
      | Some (FStar_Util.Inr (se,None )) ->
          let uu____3128 = effect_signature se  in
          (match uu____3128 with
           | None  -> None
           | Some (uvs,t) ->
               let uu____3143 =
                 let uu____3146 =
                   FStar_Syntax_Subst.set_use_range
                     (FStar_Ident.range_of_lid ftv) t
                    in
                 (uvs, uu____3146)  in
               Some uu____3143)
      | uu____3149 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3167 = try_lookup_effect_lid' env ftv  in
      FStar_Util.map_opt uu____3167 Prims.snd
  
let lookup_effect_lid' :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun ftv  ->
      let uu____3183 = try_lookup_effect_lid' env ftv  in
      match uu____3183 with
      | None  ->
          let uu____3191 =
            let uu____3192 =
              let uu____3195 = name_not_found "lookup_effect_lid'" ftv  in
              (uu____3195, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3192  in
          Prims.raise uu____3191
      | Some k -> k
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____3209 = try_lookup_effect_lid env ftv  in
      match uu____3209 with
      | None  ->
          let uu____3211 =
            let uu____3212 =
              let uu____3215 = name_not_found "lookup_effect_lid" ftv  in
              (uu____3215, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3212  in
          Prims.raise uu____3211
      | Some k -> k
  
let lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes Prims.option ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option
  =
  fun env  ->
    fun univ_insts_opt  ->
      fun lid0  ->
        let uu____3231 = lookup_qname env lid0  in
        match uu____3231 with
        | Some (FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_effect_abbrev
             (lid,univs1,binders,c,quals,uu____3248,uu____3249),None ))
            ->
            let lid1 =
              let uu____3268 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____3268  in
            let uu____3269 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_3271  ->
                      match uu___102_3271 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3272 -> false))
               in
            if uu____3269
            then None
            else
              (let insts univ_insts =
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
                     (let uu____3296 =
                        let uu____3297 =
                          FStar_Syntax_Print.lid_to_string lid1  in
                        let uu____3298 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3297 uu____3298
                         in
                      failwith uu____3296)
                  in
               match (binders, univs1) with
               | ([],uu____3305) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3314,uu____3315::uu____3316::uu____3317) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3320 =
                     let uu____3321 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____3322 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3321 uu____3322
                      in
                   failwith uu____3320
               | uu____3328 ->
                   let t =
                     match univ_insts_opt with
                     | None  -> FStar_Syntax_Util.arrow binders c
                     | Some univ_insts ->
                         let uu____3333 =
                           let uu____3334 = FStar_Syntax_Util.arrow binders c
                              in
                           (univs1, uu____3334)  in
                         let uu____3335 = insts univ_insts  in
                         inst_tscheme_with uu____3333 uu____3335
                      in
                   let t1 =
                     FStar_Syntax_Subst.set_use_range
                       (FStar_Ident.range_of_lid lid1) t
                      in
                   let uu____3337 =
                     let uu____3338 = FStar_Syntax_Subst.compress t1  in
                     uu____3338.FStar_Syntax_Syntax.n  in
                   (match uu____3337 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                        Some (binders1, c1)
                    | uu____3368 -> failwith "Impossible"))
        | uu____3372 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3396 = lookup_effect_abbrev env None l1  in
        match uu____3396 with
        | None  -> None
        | Some (uu____3403,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3408 = find1 l2  in
            (match uu____3408 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____3413 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3413 with
        | Some l1 -> l1
        | None  ->
            let uu____3416 = find1 l  in
            (match uu____3416 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____3428 = lookup_qname env l1  in
      match uu____3428 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____3439),uu____3440)) ->
          ne.FStar_Syntax_Syntax.qualifiers
      | uu____3455 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3476 =
          let uu____3477 =
            let uu____3478 = FStar_Util.string_of_int i  in
            let uu____3479 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3478 uu____3479
             in
          failwith uu____3477  in
        let uu____3480 = lookup_datacon env lid  in
        match uu____3480 with
        | (uu____3483,t) ->
            let uu____3485 =
              let uu____3486 = FStar_Syntax_Subst.compress t  in
              uu____3486.FStar_Syntax_Syntax.n  in
            (match uu____3485 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3490) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____3511 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right uu____3511 Prims.fst)
             | uu____3516 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3523 = lookup_qname env l  in
      match uu____3523 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3532,uu____3533,uu____3534,quals,uu____3536),uu____3537))
          ->
          FStar_Util.for_some
            (fun uu___103_3554  ->
               match uu___103_3554 with
               | FStar_Syntax_Syntax.Projector uu____3555 -> true
               | uu____3558 -> false) quals
      | uu____3559 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3574 = lookup_qname env lid  in
      match uu____3574 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____3583,uu____3584,uu____3585,uu____3586,uu____3587,uu____3588,uu____3589,uu____3590),uu____3591))
          -> true
      | uu____3610 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3625 = lookup_qname env lid  in
      match uu____3625 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3634,uu____3635,uu____3636,uu____3637,uu____3638,uu____3639,tags,uu____3641),uu____3642))
          ->
          FStar_Util.for_some
            (fun uu___104_3663  ->
               match uu___104_3663 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3666 -> false) tags
      | uu____3667 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3682 = lookup_qname env lid  in
      match uu____3682 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_let
           (uu____3691,uu____3692,uu____3693,tags,uu____3695),uu____3696))
          ->
          FStar_Util.for_some
            (fun uu___105_3717  ->
               match uu___105_3717 with
               | FStar_Syntax_Syntax.Action uu____3718 -> true
               | uu____3719 -> false) tags
      | uu____3720 -> false
  
let is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool =
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
    FStar_Syntax_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____3737 =
        let uu____3738 = FStar_Syntax_Util.un_uinst head1  in
        uu____3738.FStar_Syntax_Syntax.n  in
      match uu____3737 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3742 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper uu___106_3760 =
        match uu___106_3760 with
        | FStar_Util.Inl uu____3769 -> Some false
        | FStar_Util.Inr (se,uu____3778) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____3787,uu____3788,uu____3789,qs,uu____3791) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____3794 -> Some true
             | uu____3806 -> Some false)
         in
      let uu____3807 =
        let uu____3809 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____3809 mapper  in
      match uu____3807 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____3832 = lookup_qname env lid  in
      match uu____3832 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3841,uu____3842,tps,uu____3844,uu____3845,uu____3846,uu____3847,uu____3848),uu____3849))
          -> FStar_List.length tps
      | uu____3873 ->
          let uu____3882 =
            let uu____3883 =
              let uu____3886 = name_not_found "num_inductive_ty_params" lid
                 in
              (uu____3886, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3883  in
          Prims.raise uu____3882
  
let comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____3908 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____3916 =
        lookup_effect_abbrev env (Some (c.FStar_Syntax_Syntax.comp_univs))
          c.FStar_Syntax_Syntax.comp_typ_name
         in
      match uu____3916 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____3926 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____3926 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    (FStar_List.length c.FStar_Syntax_Syntax.effect_args)
                then
                  (let uu____3942 =
                     let uu____3943 =
                       let uu____3946 =
                         let uu____3947 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____3953 =
                           FStar_Util.string_of_int
                             (FStar_List.length
                                c.FStar_Syntax_Syntax.effect_args)
                            in
                         let uu____3961 =
                           let uu____3962 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____3962  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____3947 uu____3953 uu____3961
                          in
                       (uu____3946, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____3943  in
                   Prims.raise uu____3942)
                else ();
                (let inst1 =
                   FStar_List.map2
                     (fun uu____3972  ->
                        fun uu____3973  ->
                          match (uu____3972, uu____3973) with
                          | ((x,uu____3987),(t,uu____3989)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     c.FStar_Syntax_Syntax.effect_args
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____4004 =
                     let uu___115_4005 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_typ_name =
                         (uu___115_4005.FStar_Syntax_Syntax.comp_typ_name);
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___115_4005.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___115_4005.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____4004
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let result_typ : env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun comp  ->
      match comp.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
      | uu____4025 ->
          let ct = unfold_effect_abbrev env comp  in
          if
            (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Tot_lid)
              ||
              (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                 FStar_Syntax_Const.effect_GTot_lid)
          then
            let uu____4027 = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args
               in
            FStar_All.pipe_left Prims.fst uu____4027
          else
            (let uu____4045 =
               FStar_List.nth ct.FStar_Syntax_Syntax.effect_args
                 ((FStar_List.length ct.FStar_Syntax_Syntax.effect_args) -
                    (Prims.parse_int "2"))
                in
             FStar_All.pipe_left Prims.fst uu____4045)
  
let rec non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____4075 =
        let uu____4076 = FStar_Syntax_Util.unrefine t  in
        uu____4076.FStar_Syntax_Syntax.n  in
      match uu____4075 with
      | FStar_Syntax_Syntax.Tm_type uu____4079 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____4082) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4098) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____4103,c) ->
          (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
            (let uu____4115 = result_typ env c  in
             non_informative env uu____4115)
      | uu____4116 -> false
  
let comp_as_normal_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> normal_comp_typ =
  fun env  ->
    fun c  ->
      let ct = unfold_effect_abbrev env c  in
      let rec aux uu___107_4140 =
        match uu___107_4140 with
        | [] ->
            let uu____4156 =
              FStar_Util.format1
                "Expected at least two arguments to comp_typ (%s)"
                (FStar_Ident.text_of_lid ct.FStar_Syntax_Syntax.comp_typ_name)
               in
            failwith uu____4156
        | res::[] ->
            let uu____4174 =
              let uu____4175 =
                FStar_Syntax_Print.term_to_string (Prims.fst res)  in
              FStar_Util.format2
                "Expected at least two arguments to comp_typ (%s) got %s"
                (FStar_Ident.text_of_lid ct.FStar_Syntax_Syntax.comp_typ_name)
                uu____4175
               in
            failwith uu____4174
        | res::wp::[] -> ([], res, wp)
        | hd1::rest ->
            let uu____4216 = aux rest  in
            (match uu____4216 with | (i,res,wp) -> ((hd1 :: i), res, wp))
         in
      let uu____4263 = aux ct.FStar_Syntax_Syntax.effect_args  in
      match uu____4263 with
      | (indices,result,wp) ->
          {
            nct_name = (ct.FStar_Syntax_Syntax.comp_typ_name);
            nct_univs = (ct.FStar_Syntax_Syntax.comp_univs);
            nct_indices = indices;
            nct_result = result;
            nct_wp = wp;
            nct_flags = (ct.FStar_Syntax_Syntax.flags)
          }
  
let normal_comp_typ_as_comp :
  env -> normal_comp_typ -> FStar_Syntax_Syntax.comp =
  fun env  ->
    fun nct  ->
      let ct =
        {
          FStar_Syntax_Syntax.comp_typ_name = (nct.nct_name);
          FStar_Syntax_Syntax.comp_univs = (nct.nct_univs);
          FStar_Syntax_Syntax.effect_args =
            (FStar_List.append nct.nct_indices [nct.nct_result; nct.nct_wp]);
          FStar_Syntax_Syntax.flags = (nct.nct_flags)
        }  in
      FStar_Syntax_Syntax.mk_Comp ct
  
let lcomp_of_comp :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp =
  fun env  ->
    fun c0  ->
      let ct0 = comp_to_comp_typ env c0  in
      if
        (FStar_Ident.lid_equals ct0.FStar_Syntax_Syntax.comp_typ_name
           FStar_Syntax_Const.effect_Tot_lid)
          ||
          (FStar_Ident.lid_equals ct0.FStar_Syntax_Syntax.comp_typ_name
             FStar_Syntax_Const.effect_GTot_lid)
      then
        let uu____4309 =
          let uu____4312 = FStar_List.hd ct0.FStar_Syntax_Syntax.effect_args
             in
          FStar_All.pipe_left Prims.fst uu____4312  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (ct0.FStar_Syntax_Syntax.comp_typ_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (ct0.FStar_Syntax_Syntax.comp_univs);
          FStar_Syntax_Syntax.lcomp_indices = [];
          FStar_Syntax_Syntax.lcomp_res_typ = uu____4309;
          FStar_Syntax_Syntax.lcomp_cflags = (ct0.FStar_Syntax_Syntax.flags);
          FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____4333  -> c0)
        }
      else
        (let nct = comp_as_normal_comp_typ env c0  in
         {
           FStar_Syntax_Syntax.lcomp_name = (nct.nct_name);
           FStar_Syntax_Syntax.lcomp_univs = (nct.nct_univs);
           FStar_Syntax_Syntax.lcomp_indices = (nct.nct_indices);
           FStar_Syntax_Syntax.lcomp_res_typ = (Prims.fst nct.nct_result);
           FStar_Syntax_Syntax.lcomp_cflags = (nct.nct_flags);
           FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____4338  -> c0)
         })
  
let set_result_typ :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun c  ->
      fun t  ->
        let ct = comp_to_comp_typ env c  in
        if
          (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
             FStar_Syntax_Const.effect_Tot_lid)
            ||
            (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_GTot_lid)
        then
          let uu____4349 =
            let uu___116_4350 = ct  in
            let uu____4351 =
              let uu____4357 = FStar_Syntax_Syntax.as_arg t  in [uu____4357]
               in
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (uu___116_4350.FStar_Syntax_Syntax.comp_typ_name);
              FStar_Syntax_Syntax.comp_univs =
                (uu___116_4350.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_args = uu____4351;
              FStar_Syntax_Syntax.flags =
                (uu___116_4350.FStar_Syntax_Syntax.flags)
            }  in
          FStar_Syntax_Syntax.mk_Comp uu____4349
        else
          (let nct = comp_as_normal_comp_typ env c  in
           let nct1 =
             let uu___117_4361 = nct  in
             let uu____4362 = FStar_Syntax_Syntax.as_arg t  in
             {
               nct_name = (uu___117_4361.nct_name);
               nct_univs = (uu___117_4361.nct_univs);
               nct_indices = (uu___117_4361.nct_indices);
               nct_result = uu____4362;
               nct_wp = (uu___117_4361.nct_wp);
               nct_flags = (uu___117_4361.nct_flags)
             }  in
           normal_comp_typ_as_comp env nct1)
  
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____4407 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____4420 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____4420  in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let uu____4436 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____4436, uv1)
  
let new_uvar_for_env :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____4465 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____4466 = current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____4466)
           in
        if uu____4465 then all_binders env else t_binders env  in
      let uu____4468 = get_range env  in new_uvar uu____4468 bs k
  
let effect_decl_opt :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl Prims.option =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4485 = effect_decl_opt env l  in
      match uu____4485 with
      | None  ->
          let uu____4487 =
            let uu____4488 =
              let uu____4491 = name_not_found "get_effect_decl" l  in
              (uu____4491, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____4488  in
          Prims.raise uu____4487
      | Some md -> md
  
let join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let l11 = norm_eff_name env l1  in
        let l21 = norm_eff_name env l2  in
        if FStar_Ident.lid_equals l11 l21
        then let id x = x  in (l11, id, id)
        else
          if
            ((FStar_Ident.lid_equals l11 FStar_Syntax_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l21 FStar_Syntax_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l21 FStar_Syntax_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l11
                    FStar_Syntax_Const.effect_Tot_lid))
          then
            (let lift_gtot nct =
               let uu___118_4529 = nct  in
               {
                 nct_name = FStar_Syntax_Const.effect_GTot_lid;
                 nct_univs = (uu___118_4529.nct_univs);
                 nct_indices = (uu___118_4529.nct_indices);
                 nct_result = (uu___118_4529.nct_result);
                 nct_wp = (uu___118_4529.nct_wp);
                 nct_flags = (uu___118_4529.nct_flags)
               }  in
             (FStar_Syntax_Const.effect_GTot_lid, lift_gtot, lift_gtot))
          else
            (let uu____4535 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4559  ->
                       match uu____4559 with
                       | (m1,m2,uu____4567,uu____4568,uu____4569) ->
                           (FStar_Ident.lid_equals l11 m1) &&
                             (FStar_Ident.lid_equals l21 m2)))
                in
             match uu____4535 with
             | None  ->
                 let uu____4578 =
                   let uu____4579 =
                     let uu____4582 =
                       let uu____4583 = FStar_Syntax_Print.lid_to_string l11
                          in
                       let uu____4584 = FStar_Syntax_Print.lid_to_string l21
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4583
                         uu____4584
                        in
                     (uu____4582, (env.range))  in
                   FStar_Errors.Error uu____4579  in
                 Prims.raise uu____4578
             | Some (uu____4588,uu____4589,m3,j1,j2) -> (m3, j1, j2))
  
let monad_leq :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> edge Prims.option =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid))
        then
          Some
            {
              msource = l1;
              mtarget = l2;
              mlift =
                (fun nct  ->
                   let uu___119_4615 = nct  in
                   {
                     nct_name = l2;
                     nct_univs = (uu___119_4615.nct_univs);
                     nct_indices = (uu___119_4615.nct_indices);
                     nct_result = (uu___119_4615.nct_result);
                     nct_wp = (uu___119_4615.nct_wp);
                     nct_flags = (uu___119_4615.nct_flags)
                   })
            }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  env ->
    FStar_Syntax_Syntax.eff_decl Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv *
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun decls  ->
      fun m  ->
        let uu____4635 =
          FStar_All.pipe_right decls
            (FStar_Util.find_opt
               (fun d  ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
           in
        match uu____4635 with
        | None  ->
            let uu____4644 =
              FStar_Util.format1
                "Impossible: declaration for monad %s not found"
                m.FStar_Ident.str
               in
            failwith uu____4644
        | Some md ->
            let uu____4650 =
              inst_tscheme
                ((md.FStar_Syntax_Syntax.univs),
                  (md.FStar_Syntax_Syntax.signature))
               in
            (match uu____4650 with
             | (uu____4657,s) ->
                 let s1 = FStar_Syntax_Subst.compress s  in
                 (match ((md.FStar_Syntax_Syntax.binders),
                          (s1.FStar_Syntax_Syntax.n))
                  with
                  | ([],FStar_Syntax_Syntax.Tm_arrow
                     ((a,uu____4665)::(wp,uu____4667)::[],c)) when
                      let uu____4687 = result_typ env c  in
                      FStar_Syntax_Syntax.is_teff uu____4687 ->
                      (a, (wp.FStar_Syntax_Syntax.sort))
                  | uu____4690 -> failwith "Impossible"))
  
let wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  = fun env  -> fun m  -> wp_sig_aux env (env.effects).decls m 
let null_wp_for_eff :
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
              (let eff_name1 = norm_eff_name env eff_name  in
               let ed = get_effect_decl env eff_name1  in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp
                  in
               let null_wp_res =
                 let uu____4725 = get_range env  in
                 let uu____4726 =
                   let uu____4729 =
                     let uu____4730 =
                       let uu____4740 =
                         let uu____4742 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____4742]  in
                       (null_wp, uu____4740)  in
                     FStar_Syntax_Syntax.Tm_app uu____4730  in
                   FStar_Syntax_Syntax.mk uu____4729  in
                 uu____4726 None uu____4725  in
               let uu____4752 =
                 let uu____4753 =
                   let uu____4759 = FStar_Syntax_Syntax.as_arg res_t  in
                   let uu____4760 =
                     let uu____4762 = FStar_Syntax_Syntax.as_arg null_wp_res
                        in
                     [uu____4762]  in
                   uu____4759 :: uu____4760  in
                 {
                   FStar_Syntax_Syntax.comp_typ_name = eff_name1;
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_args = uu____4753;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____4752)
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____4787 = push1 x rest1  in local :: uu____4787
         in
      let uu___120_4789 = env  in
      let uu____4790 = push1 s env.gamma  in
      {
        solver = (uu___120_4789.solver);
        range = (uu___120_4789.range);
        curmodule = (uu___120_4789.curmodule);
        gamma = uu____4790;
        gamma_cache = (uu___120_4789.gamma_cache);
        modules = (uu___120_4789.modules);
        expected_typ = (uu___120_4789.expected_typ);
        sigtab = (uu___120_4789.sigtab);
        is_pattern = (uu___120_4789.is_pattern);
        instantiate_imp = (uu___120_4789.instantiate_imp);
        effects = (uu___120_4789.effects);
        generalize = (uu___120_4789.generalize);
        letrecs = (uu___120_4789.letrecs);
        top_level = (uu___120_4789.top_level);
        check_uvars = (uu___120_4789.check_uvars);
        use_eq = (uu___120_4789.use_eq);
        is_iface = (uu___120_4789.is_iface);
        admit = (uu___120_4789.admit);
        lax = (uu___120_4789.lax);
        lax_universes = (uu___120_4789.lax_universes);
        type_of = (uu___120_4789.type_of);
        universe_of = (uu___120_4789.universe_of);
        use_bv_sorts = (uu___120_4789.use_bv_sorts);
        qname_and_index = (uu___120_4789.qname_and_index)
      }
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      push_in_gamma env
        (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
  
let push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        push_in_gamma env
          (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
  
let push_local_binding : env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___121_4815 = env  in
      {
        solver = (uu___121_4815.solver);
        range = (uu___121_4815.range);
        curmodule = (uu___121_4815.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___121_4815.gamma_cache);
        modules = (uu___121_4815.modules);
        expected_typ = (uu___121_4815.expected_typ);
        sigtab = (uu___121_4815.sigtab);
        is_pattern = (uu___121_4815.is_pattern);
        instantiate_imp = (uu___121_4815.instantiate_imp);
        effects = (uu___121_4815.effects);
        generalize = (uu___121_4815.generalize);
        letrecs = (uu___121_4815.letrecs);
        top_level = (uu___121_4815.top_level);
        check_uvars = (uu___121_4815.check_uvars);
        use_eq = (uu___121_4815.use_eq);
        is_iface = (uu___121_4815.is_iface);
        admit = (uu___121_4815.admit);
        lax = (uu___121_4815.lax);
        lax_universes = (uu___121_4815.lax_universes);
        type_of = (uu___121_4815.type_of);
        universe_of = (uu___121_4815.universe_of);
        use_bv_sorts = (uu___121_4815.use_bv_sorts);
        qname_and_index = (uu___121_4815.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4831  ->
             match uu____4831 with | (x,uu____4835) -> push_bv env1 x) env bs
  
let binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___122_4855 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4855.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4855.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (Prims.snd t)
            }  in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let push_module : env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___123_4885 = env  in
       {
         solver = (uu___123_4885.solver);
         range = (uu___123_4885.range);
         curmodule = (uu___123_4885.curmodule);
         gamma = [];
         gamma_cache = (uu___123_4885.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___123_4885.sigtab);
         is_pattern = (uu___123_4885.is_pattern);
         instantiate_imp = (uu___123_4885.instantiate_imp);
         effects = (uu___123_4885.effects);
         generalize = (uu___123_4885.generalize);
         letrecs = (uu___123_4885.letrecs);
         top_level = (uu___123_4885.top_level);
         check_uvars = (uu___123_4885.check_uvars);
         use_eq = (uu___123_4885.use_eq);
         is_iface = (uu___123_4885.is_iface);
         admit = (uu___123_4885.admit);
         lax = (uu___123_4885.lax);
         lax_universes = (uu___123_4885.lax_universes);
         type_of = (uu___123_4885.type_of);
         universe_of = (uu___123_4885.universe_of);
         use_bv_sorts = (uu___123_4885.use_bv_sorts);
         qname_and_index = (uu___123_4885.qname_and_index)
       })
  
let push_univ_vars : env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___124_4900 = env  in
      {
        solver = (uu___124_4900.solver);
        range = (uu___124_4900.range);
        curmodule = (uu___124_4900.curmodule);
        gamma = (uu___124_4900.gamma);
        gamma_cache = (uu___124_4900.gamma_cache);
        modules = (uu___124_4900.modules);
        expected_typ = (Some t);
        sigtab = (uu___124_4900.sigtab);
        is_pattern = (uu___124_4900.is_pattern);
        instantiate_imp = (uu___124_4900.instantiate_imp);
        effects = (uu___124_4900.effects);
        generalize = (uu___124_4900.generalize);
        letrecs = (uu___124_4900.letrecs);
        top_level = (uu___124_4900.top_level);
        check_uvars = (uu___124_4900.check_uvars);
        use_eq = false;
        is_iface = (uu___124_4900.is_iface);
        admit = (uu___124_4900.admit);
        lax = (uu___124_4900.lax);
        lax_universes = (uu___124_4900.lax_universes);
        type_of = (uu___124_4900.type_of);
        universe_of = (uu___124_4900.universe_of);
        use_bv_sorts = (uu___124_4900.use_bv_sorts);
        qname_and_index = (uu___124_4900.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let uu____4916 = expected_typ env_  in
    ((let uu___125_4919 = env_  in
      {
        solver = (uu___125_4919.solver);
        range = (uu___125_4919.range);
        curmodule = (uu___125_4919.curmodule);
        gamma = (uu___125_4919.gamma);
        gamma_cache = (uu___125_4919.gamma_cache);
        modules = (uu___125_4919.modules);
        expected_typ = None;
        sigtab = (uu___125_4919.sigtab);
        is_pattern = (uu___125_4919.is_pattern);
        instantiate_imp = (uu___125_4919.instantiate_imp);
        effects = (uu___125_4919.effects);
        generalize = (uu___125_4919.generalize);
        letrecs = (uu___125_4919.letrecs);
        top_level = (uu___125_4919.top_level);
        check_uvars = (uu___125_4919.check_uvars);
        use_eq = false;
        is_iface = (uu___125_4919.is_iface);
        admit = (uu___125_4919.admit);
        lax = (uu___125_4919.lax);
        lax_universes = (uu___125_4919.lax_universes);
        type_of = (uu___125_4919.type_of);
        universe_of = (uu___125_4919.universe_of);
        use_bv_sorts = (uu___125_4919.use_bv_sorts);
        qname_and_index = (uu___125_4919.qname_and_index)
      }), uu____4916)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____4930 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_4934  ->
                    match uu___108_4934 with
                    | Binding_sig (uu____4936,se) -> [se]
                    | uu____4940 -> []))
             in
          FStar_All.pipe_right uu____4930 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___126_4945 = env  in
       {
         solver = (uu___126_4945.solver);
         range = (uu___126_4945.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___126_4945.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___126_4945.expected_typ);
         sigtab = (uu___126_4945.sigtab);
         is_pattern = (uu___126_4945.is_pattern);
         instantiate_imp = (uu___126_4945.instantiate_imp);
         effects = (uu___126_4945.effects);
         generalize = (uu___126_4945.generalize);
         letrecs = (uu___126_4945.letrecs);
         top_level = (uu___126_4945.top_level);
         check_uvars = (uu___126_4945.check_uvars);
         use_eq = (uu___126_4945.use_eq);
         is_iface = (uu___126_4945.is_iface);
         admit = (uu___126_4945.admit);
         lax = (uu___126_4945.lax);
         lax_universes = (uu___126_4945.lax_universes);
         type_of = (uu___126_4945.type_of);
         universe_of = (uu___126_4945.universe_of);
         use_bv_sorts = (uu___126_4945.use_bv_sorts);
         qname_and_index = (uu___126_4945.qname_and_index)
       })
  
let dummy_solver : solver_t =
  {
    init = (fun uu____4946  -> ());
    push = (fun uu____4947  -> ());
    pop = (fun uu____4948  -> ());
    mark = (fun uu____4949  -> ());
    reset_mark = (fun uu____4950  -> ());
    commit_mark = (fun uu____4951  -> ());
    encode_modul = (fun uu____4952  -> fun uu____4953  -> ());
    encode_sig = (fun uu____4954  -> fun uu____4955  -> ());
    solve = (fun uu____4956  -> fun uu____4957  -> fun uu____4958  -> ());
    is_trivial = (fun uu____4962  -> fun uu____4963  -> false);
    finish = (fun uu____4964  -> ());
    refresh = (fun uu____4965  -> ())
  } 