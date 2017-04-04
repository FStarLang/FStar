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
and edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: env -> normal_comp_typ -> normal_comp_typ }
and effects =
  {
  decls: FStar_Syntax_Syntax.eff_decl Prims.list ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident *
      (env -> normal_comp_typ -> normal_comp_typ) *
      (env -> normal_comp_typ -> normal_comp_typ)) Prims.list
    }
type implicits =
  (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term *
    FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list
type mlift = env -> normal_comp_typ -> normal_comp_typ
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
      | uu____846 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____856 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____864 =
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
          let uu____903 = new_gamma_cache ()  in
          let uu____905 = new_sigtab ()  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____903;
            modules = [];
            expected_typ = None;
            sigtab = uu____905;
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
  fun uu____953  ->
    let uu____954 = FStar_ST.read query_indices  in
    match uu____954 with
    | [] -> failwith "Empty query indices!"
    | uu____968 ->
        let uu____973 =
          let uu____978 =
            let uu____982 = FStar_ST.read query_indices  in
            FStar_List.hd uu____982  in
          let uu____996 = FStar_ST.read query_indices  in uu____978 ::
            uu____996
           in
        FStar_ST.write query_indices uu____973
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____1018  ->
    let uu____1019 = FStar_ST.read query_indices  in
    match uu____1019 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____1055  ->
    match uu____1055 with
    | (l,n1) ->
        let uu____1060 = FStar_ST.read query_indices  in
        (match uu____1060 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1094 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1104  ->
    let uu____1105 = FStar_ST.read query_indices  in FStar_List.hd uu____1105
  
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1121  ->
    let uu____1122 = FStar_ST.read query_indices  in
    match uu____1122 with
    | hd1::uu____1134::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1161 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____1175 =
       let uu____1177 = FStar_ST.read stack  in env :: uu____1177  in
     FStar_ST.write stack uu____1175);
    (let uu___109_1185 = env  in
     let uu____1186 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____1188 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___109_1185.solver);
       range = (uu___109_1185.range);
       curmodule = (uu___109_1185.curmodule);
       gamma = (uu___109_1185.gamma);
       gamma_cache = uu____1186;
       modules = (uu___109_1185.modules);
       expected_typ = (uu___109_1185.expected_typ);
       sigtab = uu____1188;
       is_pattern = (uu___109_1185.is_pattern);
       instantiate_imp = (uu___109_1185.instantiate_imp);
       effects = (uu___109_1185.effects);
       generalize = (uu___109_1185.generalize);
       letrecs = (uu___109_1185.letrecs);
       top_level = (uu___109_1185.top_level);
       check_uvars = (uu___109_1185.check_uvars);
       use_eq = (uu___109_1185.use_eq);
       is_iface = (uu___109_1185.is_iface);
       admit = (uu___109_1185.admit);
       lax = (uu___109_1185.lax);
       lax_universes = (uu___109_1185.lax_universes);
       type_of = (uu___109_1185.type_of);
       universe_of = (uu___109_1185.universe_of);
       use_bv_sorts = (uu___109_1185.use_bv_sorts);
       qname_and_index = (uu___109_1185.qname_and_index)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1192  ->
    let uu____1193 = FStar_ST.read stack  in
    match uu____1193 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1205 -> failwith "Impossible: Too many pops"
  
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
    (let uu____1237 = pop_stack ()  in ());
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
        let uu____1256 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1268  ->
                  match uu____1268 with
                  | (m,uu____1272) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1256 with
         | None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___110_1277 = env  in
               {
                 solver = (uu___110_1277.solver);
                 range = (uu___110_1277.range);
                 curmodule = (uu___110_1277.curmodule);
                 gamma = (uu___110_1277.gamma);
                 gamma_cache = (uu___110_1277.gamma_cache);
                 modules = (uu___110_1277.modules);
                 expected_typ = (uu___110_1277.expected_typ);
                 sigtab = (uu___110_1277.sigtab);
                 is_pattern = (uu___110_1277.is_pattern);
                 instantiate_imp = (uu___110_1277.instantiate_imp);
                 effects = (uu___110_1277.effects);
                 generalize = (uu___110_1277.generalize);
                 letrecs = (uu___110_1277.letrecs);
                 top_level = (uu___110_1277.top_level);
                 check_uvars = (uu___110_1277.check_uvars);
                 use_eq = (uu___110_1277.use_eq);
                 is_iface = (uu___110_1277.is_iface);
                 admit = (uu___110_1277.admit);
                 lax = (uu___110_1277.lax);
                 lax_universes = (uu___110_1277.lax_universes);
                 type_of = (uu___110_1277.type_of);
                 universe_of = (uu___110_1277.universe_of);
                 use_bv_sorts = (uu___110_1277.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1280,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___111_1286 = env  in
               {
                 solver = (uu___111_1286.solver);
                 range = (uu___111_1286.range);
                 curmodule = (uu___111_1286.curmodule);
                 gamma = (uu___111_1286.gamma);
                 gamma_cache = (uu___111_1286.gamma_cache);
                 modules = (uu___111_1286.modules);
                 expected_typ = (uu___111_1286.expected_typ);
                 sigtab = (uu___111_1286.sigtab);
                 is_pattern = (uu___111_1286.is_pattern);
                 instantiate_imp = (uu___111_1286.instantiate_imp);
                 effects = (uu___111_1286.effects);
                 generalize = (uu___111_1286.generalize);
                 letrecs = (uu___111_1286.letrecs);
                 top_level = (uu___111_1286.top_level);
                 check_uvars = (uu___111_1286.check_uvars);
                 use_eq = (uu___111_1286.use_eq);
                 is_iface = (uu___111_1286.is_iface);
                 admit = (uu___111_1286.admit);
                 lax = (uu___111_1286.lax);
                 lax_universes = (uu___111_1286.lax_universes);
                 type_of = (uu___111_1286.type_of);
                 universe_of = (uu___111_1286.universe_of);
                 use_bv_sorts = (uu___111_1286.use_bv_sorts);
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
        (let uu___112_1302 = e  in
         {
           solver = (uu___112_1302.solver);
           range = r;
           curmodule = (uu___112_1302.curmodule);
           gamma = (uu___112_1302.gamma);
           gamma_cache = (uu___112_1302.gamma_cache);
           modules = (uu___112_1302.modules);
           expected_typ = (uu___112_1302.expected_typ);
           sigtab = (uu___112_1302.sigtab);
           is_pattern = (uu___112_1302.is_pattern);
           instantiate_imp = (uu___112_1302.instantiate_imp);
           effects = (uu___112_1302.effects);
           generalize = (uu___112_1302.generalize);
           letrecs = (uu___112_1302.letrecs);
           top_level = (uu___112_1302.top_level);
           check_uvars = (uu___112_1302.check_uvars);
           use_eq = (uu___112_1302.use_eq);
           is_iface = (uu___112_1302.is_iface);
           admit = (uu___112_1302.admit);
           lax = (uu___112_1302.lax);
           lax_universes = (uu___112_1302.lax_universes);
           type_of = (uu___112_1302.type_of);
           universe_of = (uu___112_1302.universe_of);
           use_bv_sorts = (uu___112_1302.use_bv_sorts);
           qname_and_index = (uu___112_1302.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___113_1319 = env  in
      {
        solver = (uu___113_1319.solver);
        range = (uu___113_1319.range);
        curmodule = lid;
        gamma = (uu___113_1319.gamma);
        gamma_cache = (uu___113_1319.gamma_cache);
        modules = (uu___113_1319.modules);
        expected_typ = (uu___113_1319.expected_typ);
        sigtab = (uu___113_1319.sigtab);
        is_pattern = (uu___113_1319.is_pattern);
        instantiate_imp = (uu___113_1319.instantiate_imp);
        effects = (uu___113_1319.effects);
        generalize = (uu___113_1319.generalize);
        letrecs = (uu___113_1319.letrecs);
        top_level = (uu___113_1319.top_level);
        check_uvars = (uu___113_1319.check_uvars);
        use_eq = (uu___113_1319.use_eq);
        is_iface = (uu___113_1319.is_iface);
        admit = (uu___113_1319.admit);
        lax = (uu___113_1319.lax);
        lax_universes = (uu___113_1319.lax_universes);
        type_of = (uu___113_1319.type_of);
        universe_of = (uu___113_1319.universe_of);
        use_bv_sorts = (uu___113_1319.use_bv_sorts);
        qname_and_index = (uu___113_1319.qname_and_index)
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
    let uu____1344 = FStar_Syntax_Print.bv_to_string v1  in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1344
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1347  ->
    let uu____1348 = FStar_Unionfind.fresh None  in
    FStar_Syntax_Syntax.U_unif uu____1348
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.term
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> t
      | ((formals,t),uu____1366) ->
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
  fun uu___95_1386  ->
    match uu___95_1386 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1400  -> new_u_univ ()))
           in
        let uu____1401 = inst_tscheme_with (us, t) us'  in (us', uu____1401)
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1412 = inst_tscheme t  in
      match uu____1412 with
      | (us,t1) ->
          let uu____1419 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____1419)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1431  ->
          match uu____1431 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1445 =
                         let uu____1446 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____1449 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____1452 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____1453 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1446 uu____1449 uu____1452 uu____1453
                          in
                       failwith uu____1445)
                    else ();
                    inst_tscheme_with
                      ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                        t) insts)
               | uu____1456 ->
                   let uu____1457 =
                     let uu____1458 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1458
                      in
                   failwith uu____1457)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1462 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1466 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1470 -> false
  
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
             | ([],uu____1496) -> Maybe
             | (uu____1500,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1512 -> No  in
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
          let uu____1564 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1564 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___96_1581  ->
                   match uu___96_1581 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1600 =
                           let uu____1608 = inst_tscheme t  in
                           FStar_Util.Inl uu____1608  in
                         Some uu____1600
                       else None
                   | Binding_sig
                       (uu____1631,FStar_Syntax_Syntax.Sig_bundle
                        (ses,uu____1633,uu____1634,uu____1635))
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1645 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1645
                            then cache (FStar_Util.Inr (se, None))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1665 ->
                             Some t
                         | uu____1672 -> cache t  in
                       let uu____1673 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1673
                       then maybe_cache (FStar_Util.Inr (s, None))
                       else None
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1702 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1702
                       then Some (FStar_Util.Inr (s, (Some us)))
                       else None
                   | uu____1733 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1767 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____1767
         then
           let uu____1776 = find_in_sigtab env lid  in
           match uu____1776 with
           | Some se -> Some (FStar_Util.Inr (se, None))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1827,uu____1828,uu____1829)
          -> add_sigelts env ses
      | uu____1836 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se with
            | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1842) ->
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
            | uu____1846 -> ()))

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
      | (Binding_univ uu____1900)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____1915 =
            let uu____1919 = FStar_Syntax_Free.uvars t  in ext out uu____1919
             in
          aux uu____1915 tl1
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
          let uu____1975 =
            let uu____1977 = FStar_Syntax_Free.univs t  in ext out uu____1977
             in
          aux uu____1975 tl1
      | (Binding_sig uu____1979)::uu____1980 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____2017)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____2027 = FStar_Util.set_add uname out  in
          aux uu____2027 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____2041 =
            let uu____2043 = FStar_Syntax_Free.univnames t  in
            ext out uu____2043  in
          aux uu____2041 tl1
      | (Binding_sig uu____2045)::uu____2046 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___97_2062  ->
            match uu___97_2062 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____2074 =
      let uu____2076 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____2076
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____2074 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let t_binders :
  env -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list =
  fun env  ->
    let uu____2092 = all_binders env  in
    FStar_All.pipe_right uu____2092
      (FStar_List.filter
         (fun uu____2098  ->
            match uu____2098 with
            | (x,uu____2102) ->
                let uu____2103 =
                  let uu____2104 =
                    FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort
                     in
                  uu____2104.FStar_Syntax_Syntax.n  in
                (match uu____2103 with
                 | FStar_Syntax_Syntax.Tm_type uu____2107 -> true
                 | uu____2108 -> false)))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___98_2147  ->
             match uu___98_2147 with
             | Binding_sig (lids,uu____2151) -> FStar_List.append lids keys
             | uu____2154 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____2156  ->
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
        (fun uu___99_2171  ->
           match uu___99_2171 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some (id.FStar_Syntax_Syntax.sort)
           | uu____2178 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2193,lb::[]),uu____2195,uu____2196,uu____2197,uu____2198)
          ->
          let uu____2209 =
            inst_tscheme
              ((lb.FStar_Syntax_Syntax.lbunivs),
                (lb.FStar_Syntax_Syntax.lbtyp))
             in
          Some uu____2209
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2217,lbs),uu____2219,uu____2220,uu____2221,uu____2222) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2240 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2245 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____2245
                   then
                     let uu____2249 =
                       inst_tscheme
                         ((lb.FStar_Syntax_Syntax.lbunivs),
                           (lb.FStar_Syntax_Syntax.lbtyp))
                        in
                     Some uu____2249
                   else None)
      | uu____2260 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____2273) ->
        let uu____2274 =
          let uu____2277 =
            let uu____2278 =
              FStar_Syntax_Util.maybe_tot_arrow
                ne.FStar_Syntax_Syntax.binders
                ne.FStar_Syntax_Syntax.signature
               in
            ((ne.FStar_Syntax_Syntax.univs), uu____2278)  in
          inst_tscheme uu____2277  in
        Some uu____2274
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2284,uu____2285,uu____2286,uu____2287) ->
        let uu____2292 =
          let uu____2295 =
            let uu____2296 =
              FStar_Syntax_Util.maybe_tot_arrow binders
                FStar_Syntax_Syntax.teff
               in
            (us, uu____2296)  in
          inst_tscheme uu____2295  in
        Some uu____2292
    | uu____2299 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu___100_2326 =
        match uu___100_2326 with
        | FStar_Util.Inl t -> Some t
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_datacon
             (uu____2347,uvs,t,uu____2350,uu____2351,uu____2352,uu____2353,uu____2354),None
             )
            -> let uu____2365 = inst_tscheme (uvs, t)  in Some uu____2365
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t,qs,uu____2374),None
             )
            ->
            let uu____2383 =
              let uu____2384 = in_cur_mod env l  in uu____2384 = Yes  in
            if uu____2383
            then
              let uu____2388 =
                (FStar_All.pipe_right qs
                   (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                  || env.is_iface
                 in
              (if uu____2388
               then
                 let uu____2393 = inst_tscheme (uvs, t)  in Some uu____2393
               else None)
            else (let uu____2402 = inst_tscheme (uvs, t)  in Some uu____2402)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid1,uvs,tps,k,uu____2411,uu____2412,uu____2413,uu____2414),None
             )
            ->
            (match tps with
             | [] ->
                 let uu____2432 = inst_tscheme (uvs, k)  in
                 FStar_All.pipe_left (fun _0_28  -> Some _0_28) uu____2432
             | uu____2442 ->
                 let uu____2443 =
                   let uu____2446 =
                     let uu____2447 =
                       let uu____2450 = FStar_Syntax_Syntax.mk_Total k  in
                       FStar_Syntax_Util.flat_arrow tps uu____2450  in
                     (uvs, uu____2447)  in
                   inst_tscheme uu____2446  in
                 FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____2443)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid1,uvs,tps,k,uu____2464,uu____2465,uu____2466,uu____2467),Some
             us)
            ->
            (match tps with
             | [] ->
                 let uu____2486 =
                   let uu____2489 = inst_tscheme_with (uvs, k) us  in
                   (us, uu____2489)  in
                 FStar_All.pipe_left (fun _0_30  -> Some _0_30) uu____2486
             | uu____2497 ->
                 let uu____2498 =
                   let uu____2501 =
                     let uu____2502 =
                       let uu____2503 =
                         let uu____2506 = FStar_Syntax_Syntax.mk_Total k  in
                         FStar_Syntax_Util.flat_arrow tps uu____2506  in
                       (uvs, uu____2503)  in
                     inst_tscheme_with uu____2502 us  in
                   (us, uu____2501)  in
                 FStar_All.pipe_left (fun _0_31  -> Some _0_31) uu____2498)
        | FStar_Util.Inr se ->
            (match se with
             | (FStar_Syntax_Syntax.Sig_let uu____2528,None ) ->
                 lookup_type_of_let (Prims.fst se) lid
             | uu____2539 -> effect_signature (Prims.fst se))
         in
      let uu____2544 =
        let uu____2548 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____2548 mapper  in
      match uu____2544 with
      | Some (us,t) ->
          Some
            (us,
              (let uu___114_2581 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_2581.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.tk =
                   (uu___114_2581.FStar_Syntax_Syntax.tk);
                 FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_2581.FStar_Syntax_Syntax.vars)
               }))
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2598 = lookup_qname env l  in
      match uu____2598 with | None  -> false | Some uu____2614 -> true
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun bv  ->
      let uu____2635 = try_lookup_bv env bv  in
      match uu____2635 with
      | None  ->
          let uu____2641 =
            let uu____2642 =
              let uu____2645 = variable_not_found bv  in
              let uu____2646 = FStar_Syntax_Syntax.range_of_bv bv  in
              (uu____2645, uu____2646)  in
            FStar_Errors.Error uu____2642  in
          Prims.raise uu____2641
      | Some t ->
          let uu____2652 = FStar_Syntax_Syntax.range_of_bv bv  in
          FStar_Syntax_Subst.set_use_range uu____2652 t
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2662 = try_lookup_lid_aux env l  in
      match uu____2662 with
      | None  -> None
      | Some (us,t) ->
          let uu____2687 =
            let uu____2690 =
              FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t
               in
            (us, uu____2690)  in
          Some uu____2687
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun l  ->
      let uu____2701 = try_lookup_lid env l  in
      match uu____2701 with
      | None  ->
          let uu____2709 =
            let uu____2710 =
              let uu____2713 = name_not_found "lookup_lid" l  in
              (uu____2713, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____2710  in
          Prims.raise uu____2709
      | Some (us,t) -> (us, t)
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_2727  ->
              match uu___101_2727 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2729 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2740 = lookup_qname env lid  in
      match uu____2740 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2753,uvs,t,q,uu____2757),None ))
          ->
          let uu____2773 =
            let uu____2779 =
              let uu____2782 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____2782)  in
            (uu____2779, q)  in
          Some uu____2773
      | uu____2791 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2811 = lookup_qname env lid  in
      match uu____2811 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2822,uvs,t,uu____2825,uu____2826),None ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2842 ->
          let uu____2851 =
            let uu____2852 =
              let uu____2855 = name_not_found "lookup_val_decl" lid  in
              (uu____2855, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2852  in
          Prims.raise uu____2851
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2866 = lookup_qname env lid  in
      match uu____2866 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2877,uvs,t,uu____2880,uu____2881,uu____2882,uu____2883,uu____2884),None
           ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2902 ->
          let uu____2911 =
            let uu____2912 =
              let uu____2915 = name_not_found "lookup_datacon" lid  in
              (uu____2915, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2912  in
          Prims.raise uu____2911
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____2927 = lookup_qname env lid  in
      match uu____2927 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2939,uu____2940,uu____2941,uu____2942,uu____2943,dcs,uu____2945,uu____2946),uu____2947))
          -> (true, dcs)
      | uu____2969 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____2985 = lookup_qname env lid  in
      match uu____2985 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2994,uu____2995,uu____2996,l,uu____2998,uu____2999,uu____3000,uu____3001),uu____3002))
          -> l
      | uu____3021 ->
          let uu____3030 =
            let uu____3031 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____3031  in
          failwith uu____3030
  
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
        let uu____3055 = lookup_qname env lid  in
        match uu____3055 with
        | Some (FStar_Util.Inr (se,None )) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3084,lbs),uu____3086,uu____3087,quals,uu____3089)
                 when visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____3106 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____3106
                      then
                        let uu____3111 =
                          let uu____3115 =
                            let uu____3116 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef
                               in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3116
                             in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3115)  in
                        Some uu____3111
                      else None)
             | uu____3125 -> None)
        | uu____3128 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3147 = lookup_qname env ftv  in
      match uu____3147 with
      | Some (FStar_Util.Inr (se,None )) ->
          let uu____3171 = effect_signature se  in
          (match uu____3171 with
           | None  -> None
           | Some (uu____3178,t) ->
               let uu____3182 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               Some uu____3182)
      | uu____3183 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____3198 = try_lookup_effect_lid env ftv  in
      match uu____3198 with
      | None  ->
          let uu____3200 =
            let uu____3201 =
              let uu____3204 = name_not_found "lookup_effect_lid" ftv  in
              (uu____3204, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3201  in
          Prims.raise uu____3200
      | Some k -> k
  
let lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3218 = lookup_qname env lid0  in
        match uu____3218 with
        | Some (FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_effect_abbrev
             (lid,univs1,binders,c,quals,uu____3235,uu____3236),None ))
            ->
            let lid1 =
              let uu____3255 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____3255  in
            let uu____3256 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_3258  ->
                      match uu___102_3258 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3259 -> false))
               in
            if uu____3256
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
                     (let uu____3275 =
                        let uu____3276 =
                          FStar_Syntax_Print.lid_to_string lid1  in
                        let uu____3277 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3276 uu____3277
                         in
                      failwith uu____3275)
                  in
               match (binders, univs1) with
               | ([],uu____3283) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3292,uu____3293::uu____3294::uu____3295) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3298 =
                     let uu____3299 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____3300 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3299 uu____3300
                      in
                   failwith uu____3298
               | uu____3306 ->
                   let t =
                     let uu____3310 =
                       let uu____3311 = FStar_Syntax_Util.arrow binders c  in
                       (univs1, uu____3311)  in
                     inst_tscheme_with uu____3310 insts  in
                   let t1 =
                     FStar_Syntax_Subst.set_use_range
                       (FStar_Ident.range_of_lid lid1) t
                      in
                   let uu____3313 =
                     let uu____3314 = FStar_Syntax_Subst.compress t1  in
                     uu____3314.FStar_Syntax_Syntax.n  in
                   (match uu____3313 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                        Some (binders1, c1)
                    | uu____3344 -> failwith "Impossible"))
        | uu____3348 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3372 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____3372 with
        | None  -> None
        | Some (uu____3379,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3384 = find1 l2  in
            (match uu____3384 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____3389 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3389 with
        | Some l1 -> l1
        | None  ->
            let uu____3392 = find1 l  in
            (match uu____3392 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____3404 = lookup_qname env l1  in
      match uu____3404 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____3415),uu____3416)) ->
          ne.FStar_Syntax_Syntax.qualifiers
      | uu____3431 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3452 =
          let uu____3453 =
            let uu____3454 = FStar_Util.string_of_int i  in
            let uu____3455 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3454 uu____3455
             in
          failwith uu____3453  in
        let uu____3456 = lookup_datacon env lid  in
        match uu____3456 with
        | (uu____3459,t) ->
            let uu____3461 =
              let uu____3462 = FStar_Syntax_Subst.compress t  in
              uu____3462.FStar_Syntax_Syntax.n  in
            (match uu____3461 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3466) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____3487 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right uu____3487 Prims.fst)
             | uu____3492 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3499 = lookup_qname env l  in
      match uu____3499 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3508,uu____3509,uu____3510,quals,uu____3512),uu____3513))
          ->
          FStar_Util.for_some
            (fun uu___103_3530  ->
               match uu___103_3530 with
               | FStar_Syntax_Syntax.Projector uu____3531 -> true
               | uu____3534 -> false) quals
      | uu____3535 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3550 = lookup_qname env lid  in
      match uu____3550 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____3559,uu____3560,uu____3561,uu____3562,uu____3563,uu____3564,uu____3565,uu____3566),uu____3567))
          -> true
      | uu____3586 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3601 = lookup_qname env lid  in
      match uu____3601 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3610,uu____3611,uu____3612,uu____3613,uu____3614,uu____3615,tags,uu____3617),uu____3618))
          ->
          FStar_Util.for_some
            (fun uu___104_3639  ->
               match uu___104_3639 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3642 -> false) tags
      | uu____3643 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3658 = lookup_qname env lid  in
      match uu____3658 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_let
           (uu____3667,uu____3668,uu____3669,tags,uu____3671),uu____3672))
          ->
          FStar_Util.for_some
            (fun uu___105_3693  ->
               match uu___105_3693 with
               | FStar_Syntax_Syntax.Action uu____3694 -> true
               | uu____3695 -> false) tags
      | uu____3696 -> false
  
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
      let uu____3713 =
        let uu____3714 = FStar_Syntax_Util.un_uinst head1  in
        uu____3714.FStar_Syntax_Syntax.n  in
      match uu____3713 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3718 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper uu___106_3736 =
        match uu___106_3736 with
        | FStar_Util.Inl uu____3745 -> Some false
        | FStar_Util.Inr (se,uu____3754) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____3763,uu____3764,uu____3765,qs,uu____3767) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____3770 -> Some true
             | uu____3782 -> Some false)
         in
      let uu____3783 =
        let uu____3785 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____3785 mapper  in
      match uu____3783 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____3808 = lookup_qname env lid  in
      match uu____3808 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3817,uu____3818,tps,uu____3820,uu____3821,uu____3822,uu____3823,uu____3824),uu____3825))
          -> FStar_List.length tps
      | uu____3849 ->
          let uu____3858 =
            let uu____3859 =
              let uu____3862 = name_not_found "num_inductive_ty_params" lid
                 in
              (uu____3862, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3859  in
          Prims.raise uu____3858
  
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
        | uu____3884 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____3892 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.comp_typ_name
         in
      match uu____3892 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____3902 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____3902 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    (FStar_List.length c.FStar_Syntax_Syntax.effect_args)
                then
                  (let uu____3918 =
                     let uu____3919 =
                       let uu____3922 =
                         let uu____3923 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____3929 =
                           FStar_Util.string_of_int
                             (FStar_List.length
                                c.FStar_Syntax_Syntax.effect_args)
                            in
                         let uu____3937 =
                           let uu____3938 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____3938  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____3923 uu____3929 uu____3937
                          in
                       (uu____3922, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____3919  in
                   Prims.raise uu____3918)
                else ();
                (let inst1 =
                   FStar_List.map2
                     (fun uu____3948  ->
                        fun uu____3949  ->
                          match (uu____3948, uu____3949) with
                          | ((x,uu____3963),(t,uu____3965)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     c.FStar_Syntax_Syntax.effect_args
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____3980 =
                     let uu___115_3981 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_typ_name =
                         (uu___115_3981.FStar_Syntax_Syntax.comp_typ_name);
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___115_3981.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___115_3981.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____3980
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let result_typ : env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun comp  ->
      match comp.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
      | uu____4001 ->
          let ct = unfold_effect_abbrev env comp  in
          if
            (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Tot_lid)
              ||
              (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                 FStar_Syntax_Const.effect_GTot_lid)
          then
            let uu____4003 = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args
               in
            FStar_All.pipe_left Prims.fst uu____4003
          else
            (let uu____4021 =
               FStar_List.nth ct.FStar_Syntax_Syntax.effect_args
                 ((FStar_List.length ct.FStar_Syntax_Syntax.effect_args) -
                    (Prims.parse_int "2"))
                in
             FStar_All.pipe_left Prims.fst uu____4021)
  
let rec non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____4051 =
        let uu____4052 = FStar_Syntax_Util.unrefine t  in
        uu____4052.FStar_Syntax_Syntax.n  in
      match uu____4051 with
      | FStar_Syntax_Syntax.Tm_type uu____4055 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____4058) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4074) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____4079,c) ->
          (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
            (let uu____4091 = result_typ env c  in
             non_informative env uu____4091)
      | uu____4092 -> false
  
let comp_as_normal_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> normal_comp_typ =
  fun env  ->
    fun c  ->
      let ct = unfold_effect_abbrev env c  in
      let rec aux uu___107_4116 =
        match uu___107_4116 with
        | [] ->
            let uu____4132 =
              FStar_Util.format1
                "Expected at least two arguments to comp_typ (%s)"
                (FStar_Ident.text_of_lid ct.FStar_Syntax_Syntax.comp_typ_name)
               in
            failwith uu____4132
        | res::[] ->
            let uu____4150 =
              let uu____4151 =
                FStar_Syntax_Print.term_to_string (Prims.fst res)  in
              FStar_Util.format2
                "Expected at least two arguments to comp_typ (%s) got %s"
                (FStar_Ident.text_of_lid ct.FStar_Syntax_Syntax.comp_typ_name)
                uu____4151
               in
            failwith uu____4150
        | res::wp::[] -> ([], res, wp)
        | hd1::rest ->
            let uu____4192 = aux rest  in
            (match uu____4192 with | (i,res,wp) -> ((hd1 :: i), res, wp))
         in
      let uu____4239 = aux ct.FStar_Syntax_Syntax.effect_args  in
      match uu____4239 with
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
        let uu____4285 =
          let uu____4288 = FStar_List.hd ct0.FStar_Syntax_Syntax.effect_args
             in
          FStar_All.pipe_left Prims.fst uu____4288  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (ct0.FStar_Syntax_Syntax.comp_typ_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (ct0.FStar_Syntax_Syntax.comp_univs);
          FStar_Syntax_Syntax.lcomp_indices = [];
          FStar_Syntax_Syntax.lcomp_res_typ = uu____4285;
          FStar_Syntax_Syntax.lcomp_cflags = (ct0.FStar_Syntax_Syntax.flags);
          FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____4309  -> c0)
        }
      else
        (let nct = comp_as_normal_comp_typ env c0  in
         {
           FStar_Syntax_Syntax.lcomp_name = (nct.nct_name);
           FStar_Syntax_Syntax.lcomp_univs = (nct.nct_univs);
           FStar_Syntax_Syntax.lcomp_indices = (nct.nct_indices);
           FStar_Syntax_Syntax.lcomp_res_typ = (Prims.fst nct.nct_result);
           FStar_Syntax_Syntax.lcomp_cflags = (nct.nct_flags);
           FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____4314  -> c0)
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
          let uu____4325 =
            let uu___116_4326 = ct  in
            let uu____4327 =
              let uu____4333 = FStar_Syntax_Syntax.as_arg t  in [uu____4333]
               in
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (uu___116_4326.FStar_Syntax_Syntax.comp_typ_name);
              FStar_Syntax_Syntax.comp_univs =
                (uu___116_4326.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_args = uu____4327;
              FStar_Syntax_Syntax.flags =
                (uu___116_4326.FStar_Syntax_Syntax.flags)
            }  in
          FStar_Syntax_Syntax.mk_Comp uu____4325
        else
          (let nct = comp_as_normal_comp_typ env c  in
           let nct1 =
             let uu___117_4337 = nct  in
             let uu____4338 = FStar_Syntax_Syntax.as_arg t  in
             {
               nct_name = (uu___117_4337.nct_name);
               nct_univs = (uu___117_4337.nct_univs);
               nct_indices = (uu___117_4337.nct_indices);
               nct_result = uu____4338;
               nct_wp = (uu___117_4337.nct_wp);
               nct_flags = (uu___117_4337.nct_flags)
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
        | uu____4383 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____4396 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____4396  in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let uu____4412 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____4412, uv1)
  
let new_uvar_for_env :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____4441 =
          (FStar_Options.full_context_dependency ()) ||
            (let uu____4442 = current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____4442)
           in
        if uu____4441 then all_binders env else t_binders env  in
      let uu____4444 = get_range env  in new_uvar uu____4444 bs k
  
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
      let uu____4461 = effect_decl_opt env l  in
      match uu____4461 with
      | None  ->
          let uu____4463 =
            let uu____4464 =
              let uu____4467 = name_not_found "get_effect_decl" l  in
              (uu____4467, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____4464  in
          Prims.raise uu____4463
      | Some md -> md
  
let join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then let id uu____4492 x = x  in (l1, id, id)
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
            (let lift_gtot uu____4511 nct =
               let uu___118_4513 = nct  in
               {
                 nct_name = FStar_Syntax_Const.effect_GTot_lid;
                 nct_univs = (uu___118_4513.nct_univs);
                 nct_indices = (uu___118_4513.nct_indices);
                 nct_result = (uu___118_4513.nct_result);
                 nct_wp = (uu___118_4513.nct_wp);
                 nct_flags = (uu___118_4513.nct_flags)
               }  in
             (FStar_Syntax_Const.effect_GTot_lid, lift_gtot, lift_gtot))
          else
            (let uu____4523 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4579  ->
                       match uu____4579 with
                       | (m1,m2,uu____4595,uu____4596,uu____4597) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____4523 with
             | None  ->
                 let uu____4630 =
                   let uu____4631 =
                     let uu____4634 =
                       let uu____4635 = FStar_Syntax_Print.lid_to_string l1
                          in
                       let uu____4636 = FStar_Syntax_Print.lid_to_string l2
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4635
                         uu____4636
                        in
                     (uu____4634, (env.range))  in
                   FStar_Errors.Error uu____4631  in
                 Prims.raise uu____4630
             | Some (uu____4640,uu____4641,m3,j1,j2) -> (m3, j1, j2))
  
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
                (fun env1  ->
                   fun nct  ->
                     let uu___119_4696 = nct  in
                     {
                       nct_name = l2;
                       nct_univs = (uu___119_4696.nct_univs);
                       nct_indices = (uu___119_4696.nct_indices);
                       nct_result = (uu___119_4696.nct_result);
                       nct_wp = (uu___119_4696.nct_wp);
                       nct_flags = (uu___119_4696.nct_flags)
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
        let uu____4716 =
          FStar_All.pipe_right decls
            (FStar_Util.find_opt
               (fun d  ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
           in
        match uu____4716 with
        | None  ->
            let uu____4725 =
              FStar_Util.format1
                "Impossible: declaration for monad %s not found"
                m.FStar_Ident.str
               in
            failwith uu____4725
        | Some md ->
            let uu____4731 =
              inst_tscheme
                ((md.FStar_Syntax_Syntax.univs),
                  (md.FStar_Syntax_Syntax.signature))
               in
            (match uu____4731 with
             | (uu____4738,s) ->
                 let s1 = FStar_Syntax_Subst.compress s  in
                 (match ((md.FStar_Syntax_Syntax.binders),
                          (s1.FStar_Syntax_Syntax.n))
                  with
                  | ([],FStar_Syntax_Syntax.Tm_arrow
                     ((a,uu____4746)::(wp,uu____4748)::[],c)) when
                      let uu____4768 = result_typ env c  in
                      FStar_Syntax_Syntax.is_teff uu____4768 ->
                      (a, (wp.FStar_Syntax_Syntax.sort))
                  | uu____4771 -> failwith "Impossible"))
  
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
                 let uu____4806 = get_range env  in
                 let uu____4807 =
                   let uu____4810 =
                     let uu____4811 =
                       let uu____4821 =
                         let uu____4823 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____4823]  in
                       (null_wp, uu____4821)  in
                     FStar_Syntax_Syntax.Tm_app uu____4811  in
                   FStar_Syntax_Syntax.mk uu____4810  in
                 uu____4807 None uu____4806  in
               let uu____4833 =
                 let uu____4834 =
                   let uu____4840 = FStar_Syntax_Syntax.as_arg res_t  in
                   let uu____4841 =
                     let uu____4843 = FStar_Syntax_Syntax.as_arg null_wp_res
                        in
                     [uu____4843]  in
                   uu____4840 :: uu____4841  in
                 {
                   FStar_Syntax_Syntax.comp_typ_name = eff_name1;
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_args = uu____4834;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____4833)
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____4868 = push1 x rest1  in local :: uu____4868
         in
      let uu___120_4870 = env  in
      let uu____4871 = push1 s env.gamma  in
      {
        solver = (uu___120_4870.solver);
        range = (uu___120_4870.range);
        curmodule = (uu___120_4870.curmodule);
        gamma = uu____4871;
        gamma_cache = (uu___120_4870.gamma_cache);
        modules = (uu___120_4870.modules);
        expected_typ = (uu___120_4870.expected_typ);
        sigtab = (uu___120_4870.sigtab);
        is_pattern = (uu___120_4870.is_pattern);
        instantiate_imp = (uu___120_4870.instantiate_imp);
        effects = (uu___120_4870.effects);
        generalize = (uu___120_4870.generalize);
        letrecs = (uu___120_4870.letrecs);
        top_level = (uu___120_4870.top_level);
        check_uvars = (uu___120_4870.check_uvars);
        use_eq = (uu___120_4870.use_eq);
        is_iface = (uu___120_4870.is_iface);
        admit = (uu___120_4870.admit);
        lax = (uu___120_4870.lax);
        lax_universes = (uu___120_4870.lax_universes);
        type_of = (uu___120_4870.type_of);
        universe_of = (uu___120_4870.universe_of);
        use_bv_sorts = (uu___120_4870.use_bv_sorts);
        qname_and_index = (uu___120_4870.qname_and_index)
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
      let uu___121_4896 = env  in
      {
        solver = (uu___121_4896.solver);
        range = (uu___121_4896.range);
        curmodule = (uu___121_4896.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___121_4896.gamma_cache);
        modules = (uu___121_4896.modules);
        expected_typ = (uu___121_4896.expected_typ);
        sigtab = (uu___121_4896.sigtab);
        is_pattern = (uu___121_4896.is_pattern);
        instantiate_imp = (uu___121_4896.instantiate_imp);
        effects = (uu___121_4896.effects);
        generalize = (uu___121_4896.generalize);
        letrecs = (uu___121_4896.letrecs);
        top_level = (uu___121_4896.top_level);
        check_uvars = (uu___121_4896.check_uvars);
        use_eq = (uu___121_4896.use_eq);
        is_iface = (uu___121_4896.is_iface);
        admit = (uu___121_4896.admit);
        lax = (uu___121_4896.lax);
        lax_universes = (uu___121_4896.lax_universes);
        type_of = (uu___121_4896.type_of);
        universe_of = (uu___121_4896.universe_of);
        use_bv_sorts = (uu___121_4896.use_bv_sorts);
        qname_and_index = (uu___121_4896.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____4912  ->
             match uu____4912 with | (x,uu____4916) -> push_bv env1 x) env bs
  
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
            let uu___122_4936 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4936.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4936.FStar_Syntax_Syntax.index);
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
      (let uu___123_4966 = env  in
       {
         solver = (uu___123_4966.solver);
         range = (uu___123_4966.range);
         curmodule = (uu___123_4966.curmodule);
         gamma = [];
         gamma_cache = (uu___123_4966.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___123_4966.sigtab);
         is_pattern = (uu___123_4966.is_pattern);
         instantiate_imp = (uu___123_4966.instantiate_imp);
         effects = (uu___123_4966.effects);
         generalize = (uu___123_4966.generalize);
         letrecs = (uu___123_4966.letrecs);
         top_level = (uu___123_4966.top_level);
         check_uvars = (uu___123_4966.check_uvars);
         use_eq = (uu___123_4966.use_eq);
         is_iface = (uu___123_4966.is_iface);
         admit = (uu___123_4966.admit);
         lax = (uu___123_4966.lax);
         lax_universes = (uu___123_4966.lax_universes);
         type_of = (uu___123_4966.type_of);
         universe_of = (uu___123_4966.universe_of);
         use_bv_sorts = (uu___123_4966.use_bv_sorts);
         qname_and_index = (uu___123_4966.qname_and_index)
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
      let uu___124_4981 = env  in
      {
        solver = (uu___124_4981.solver);
        range = (uu___124_4981.range);
        curmodule = (uu___124_4981.curmodule);
        gamma = (uu___124_4981.gamma);
        gamma_cache = (uu___124_4981.gamma_cache);
        modules = (uu___124_4981.modules);
        expected_typ = (Some t);
        sigtab = (uu___124_4981.sigtab);
        is_pattern = (uu___124_4981.is_pattern);
        instantiate_imp = (uu___124_4981.instantiate_imp);
        effects = (uu___124_4981.effects);
        generalize = (uu___124_4981.generalize);
        letrecs = (uu___124_4981.letrecs);
        top_level = (uu___124_4981.top_level);
        check_uvars = (uu___124_4981.check_uvars);
        use_eq = false;
        is_iface = (uu___124_4981.is_iface);
        admit = (uu___124_4981.admit);
        lax = (uu___124_4981.lax);
        lax_universes = (uu___124_4981.lax_universes);
        type_of = (uu___124_4981.type_of);
        universe_of = (uu___124_4981.universe_of);
        use_bv_sorts = (uu___124_4981.use_bv_sorts);
        qname_and_index = (uu___124_4981.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let uu____4997 = expected_typ env_  in
    ((let uu___125_5000 = env_  in
      {
        solver = (uu___125_5000.solver);
        range = (uu___125_5000.range);
        curmodule = (uu___125_5000.curmodule);
        gamma = (uu___125_5000.gamma);
        gamma_cache = (uu___125_5000.gamma_cache);
        modules = (uu___125_5000.modules);
        expected_typ = None;
        sigtab = (uu___125_5000.sigtab);
        is_pattern = (uu___125_5000.is_pattern);
        instantiate_imp = (uu___125_5000.instantiate_imp);
        effects = (uu___125_5000.effects);
        generalize = (uu___125_5000.generalize);
        letrecs = (uu___125_5000.letrecs);
        top_level = (uu___125_5000.top_level);
        check_uvars = (uu___125_5000.check_uvars);
        use_eq = false;
        is_iface = (uu___125_5000.is_iface);
        admit = (uu___125_5000.admit);
        lax = (uu___125_5000.lax);
        lax_universes = (uu___125_5000.lax_universes);
        type_of = (uu___125_5000.type_of);
        universe_of = (uu___125_5000.universe_of);
        use_bv_sorts = (uu___125_5000.use_bv_sorts);
        qname_and_index = (uu___125_5000.qname_and_index)
      }), uu____4997)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5011 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_5015  ->
                    match uu___108_5015 with
                    | Binding_sig (uu____5017,se) -> [se]
                    | uu____5021 -> []))
             in
          FStar_All.pipe_right uu____5011 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___126_5026 = env  in
       {
         solver = (uu___126_5026.solver);
         range = (uu___126_5026.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___126_5026.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___126_5026.expected_typ);
         sigtab = (uu___126_5026.sigtab);
         is_pattern = (uu___126_5026.is_pattern);
         instantiate_imp = (uu___126_5026.instantiate_imp);
         effects = (uu___126_5026.effects);
         generalize = (uu___126_5026.generalize);
         letrecs = (uu___126_5026.letrecs);
         top_level = (uu___126_5026.top_level);
         check_uvars = (uu___126_5026.check_uvars);
         use_eq = (uu___126_5026.use_eq);
         is_iface = (uu___126_5026.is_iface);
         admit = (uu___126_5026.admit);
         lax = (uu___126_5026.lax);
         lax_universes = (uu___126_5026.lax_universes);
         type_of = (uu___126_5026.type_of);
         universe_of = (uu___126_5026.universe_of);
         use_bv_sorts = (uu___126_5026.use_bv_sorts);
         qname_and_index = (uu___126_5026.qname_and_index)
       })
  
let dummy_solver : solver_t =
  {
    init = (fun uu____5027  -> ());
    push = (fun uu____5028  -> ());
    pop = (fun uu____5029  -> ());
    mark = (fun uu____5030  -> ());
    reset_mark = (fun uu____5031  -> ());
    commit_mark = (fun uu____5032  -> ());
    encode_modul = (fun uu____5033  -> fun uu____5034  -> ());
    encode_sig = (fun uu____5035  -> fun uu____5036  -> ());
    solve = (fun uu____5037  -> fun uu____5038  -> fun uu____5039  -> ());
    is_trivial = (fun uu____5043  -> fun uu____5044  -> false);
    finish = (fun uu____5045  -> ());
    refresh = (fun uu____5046  -> ())
  } 