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
          let _0_202 = new_gamma_cache ()  in
          let _0_201 = new_sigtab ()  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = _0_202;
            modules = [];
            expected_typ = None;
            sigtab = _0_201;
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
  fun uu____900  ->
    let uu____901 = FStar_ST.read query_indices  in
    match uu____901 with
    | [] -> failwith "Empty query indices!"
    | uu____915 ->
        let _0_205 =
          let _0_204 = FStar_List.hd (FStar_ST.read query_indices)  in
          let _0_203 = FStar_ST.read query_indices  in _0_204 :: _0_203  in
        FStar_ST.write query_indices _0_205
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____946  ->
    let uu____947 = FStar_ST.read query_indices  in
    match uu____947 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.write query_indices tl
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____983  ->
    match uu____983 with
    | (l,n) ->
        let uu____988 = FStar_ST.read query_indices  in
        (match uu____988 with
         | hd::tl -> FStar_ST.write query_indices (((l, n) :: hd) :: tl)
         | uu____1022 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1032  -> FStar_List.hd (FStar_ST.read query_indices) 
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1044  ->
    let uu____1045 = FStar_ST.read query_indices  in
    match uu____1045 with
    | hd::uu____1057::tl -> FStar_ST.write query_indices (hd :: tl)
    | uu____1084 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let _0_207 = let _0_206 = FStar_ST.read stack  in env :: _0_206  in
     FStar_ST.write stack _0_207);
    (let uu___109_1104 = env  in
     let _0_209 = FStar_Util.smap_copy (gamma_cache env)  in
     let _0_208 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___109_1104.solver);
       range = (uu___109_1104.range);
       curmodule = (uu___109_1104.curmodule);
       gamma = (uu___109_1104.gamma);
       gamma_cache = _0_209;
       modules = (uu___109_1104.modules);
       expected_typ = (uu___109_1104.expected_typ);
       sigtab = _0_208;
       is_pattern = (uu___109_1104.is_pattern);
       instantiate_imp = (uu___109_1104.instantiate_imp);
       effects = (uu___109_1104.effects);
       generalize = (uu___109_1104.generalize);
       letrecs = (uu___109_1104.letrecs);
       top_level = (uu___109_1104.top_level);
       check_uvars = (uu___109_1104.check_uvars);
       use_eq = (uu___109_1104.use_eq);
       is_iface = (uu___109_1104.is_iface);
       admit = (uu___109_1104.admit);
       lax = (uu___109_1104.lax);
       lax_universes = (uu___109_1104.lax_universes);
       type_of = (uu___109_1104.type_of);
       universe_of = (uu___109_1104.universe_of);
       use_bv_sorts = (uu___109_1104.use_bv_sorts);
       qname_and_index = (uu___109_1104.qname_and_index)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1107  ->
    let uu____1108 = FStar_ST.read stack  in
    match uu____1108 with
    | env::tl -> (FStar_ST.write stack tl; env)
    | uu____1120 -> failwith "Impossible: Too many pops"
  
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
    Prims.ignore (pop_stack ());
    env
  
let reset_mark : env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
  
let incr_query_index : env -> env =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qname_and_index with
    | None  -> env
    | Some (l,n) ->
        let uu____1170 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1182  ->
                  match uu____1182 with
                  | (m,uu____1186) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1170 with
         | None  ->
             let next = n + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___110_1191 = env  in
               {
                 solver = (uu___110_1191.solver);
                 range = (uu___110_1191.range);
                 curmodule = (uu___110_1191.curmodule);
                 gamma = (uu___110_1191.gamma);
                 gamma_cache = (uu___110_1191.gamma_cache);
                 modules = (uu___110_1191.modules);
                 expected_typ = (uu___110_1191.expected_typ);
                 sigtab = (uu___110_1191.sigtab);
                 is_pattern = (uu___110_1191.is_pattern);
                 instantiate_imp = (uu___110_1191.instantiate_imp);
                 effects = (uu___110_1191.effects);
                 generalize = (uu___110_1191.generalize);
                 letrecs = (uu___110_1191.letrecs);
                 top_level = (uu___110_1191.top_level);
                 check_uvars = (uu___110_1191.check_uvars);
                 use_eq = (uu___110_1191.use_eq);
                 is_iface = (uu___110_1191.is_iface);
                 admit = (uu___110_1191.admit);
                 lax = (uu___110_1191.lax);
                 lax_universes = (uu___110_1191.lax_universes);
                 type_of = (uu___110_1191.type_of);
                 universe_of = (uu___110_1191.universe_of);
                 use_bv_sorts = (uu___110_1191.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1194,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___111_1200 = env  in
               {
                 solver = (uu___111_1200.solver);
                 range = (uu___111_1200.range);
                 curmodule = (uu___111_1200.curmodule);
                 gamma = (uu___111_1200.gamma);
                 gamma_cache = (uu___111_1200.gamma_cache);
                 modules = (uu___111_1200.modules);
                 expected_typ = (uu___111_1200.expected_typ);
                 sigtab = (uu___111_1200.sigtab);
                 is_pattern = (uu___111_1200.is_pattern);
                 instantiate_imp = (uu___111_1200.instantiate_imp);
                 effects = (uu___111_1200.effects);
                 generalize = (uu___111_1200.generalize);
                 letrecs = (uu___111_1200.letrecs);
                 top_level = (uu___111_1200.top_level);
                 check_uvars = (uu___111_1200.check_uvars);
                 use_eq = (uu___111_1200.use_eq);
                 is_iface = (uu___111_1200.is_iface);
                 admit = (uu___111_1200.admit);
                 lax = (uu___111_1200.lax);
                 lax_universes = (uu___111_1200.lax_universes);
                 type_of = (uu___111_1200.type_of);
                 universe_of = (uu___111_1200.universe_of);
                 use_bv_sorts = (uu___111_1200.use_bv_sorts);
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
        (let uu___112_1216 = e  in
         {
           solver = (uu___112_1216.solver);
           range = r;
           curmodule = (uu___112_1216.curmodule);
           gamma = (uu___112_1216.gamma);
           gamma_cache = (uu___112_1216.gamma_cache);
           modules = (uu___112_1216.modules);
           expected_typ = (uu___112_1216.expected_typ);
           sigtab = (uu___112_1216.sigtab);
           is_pattern = (uu___112_1216.is_pattern);
           instantiate_imp = (uu___112_1216.instantiate_imp);
           effects = (uu___112_1216.effects);
           generalize = (uu___112_1216.generalize);
           letrecs = (uu___112_1216.letrecs);
           top_level = (uu___112_1216.top_level);
           check_uvars = (uu___112_1216.check_uvars);
           use_eq = (uu___112_1216.use_eq);
           is_iface = (uu___112_1216.is_iface);
           admit = (uu___112_1216.admit);
           lax = (uu___112_1216.lax);
           lax_universes = (uu___112_1216.lax_universes);
           type_of = (uu___112_1216.type_of);
           universe_of = (uu___112_1216.universe_of);
           use_bv_sorts = (uu___112_1216.use_bv_sorts);
           qname_and_index = (uu___112_1216.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___113_1233 = env  in
      {
        solver = (uu___113_1233.solver);
        range = (uu___113_1233.range);
        curmodule = lid;
        gamma = (uu___113_1233.gamma);
        gamma_cache = (uu___113_1233.gamma_cache);
        modules = (uu___113_1233.modules);
        expected_typ = (uu___113_1233.expected_typ);
        sigtab = (uu___113_1233.sigtab);
        is_pattern = (uu___113_1233.is_pattern);
        instantiate_imp = (uu___113_1233.instantiate_imp);
        effects = (uu___113_1233.effects);
        generalize = (uu___113_1233.generalize);
        letrecs = (uu___113_1233.letrecs);
        top_level = (uu___113_1233.top_level);
        check_uvars = (uu___113_1233.check_uvars);
        use_eq = (uu___113_1233.use_eq);
        is_iface = (uu___113_1233.is_iface);
        admit = (uu___113_1233.admit);
        lax = (uu___113_1233.lax);
        lax_universes = (uu___113_1233.lax_universes);
        type_of = (uu___113_1233.type_of);
        universe_of = (uu___113_1233.universe_of);
        use_bv_sorts = (uu___113_1233.use_bv_sorts);
        qname_and_index = (uu___113_1233.qname_and_index)
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
  fun v  ->
    let _0_210 = FStar_Syntax_Print.bv_to_string v  in
    FStar_Util.format1 "Variable \"%s\" not found" _0_210
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1260  -> FStar_Syntax_Syntax.U_unif (FStar_Unionfind.fresh None) 
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.term
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> t
      | ((formals,t),uu____1276) ->
          let n = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n - i), u)))
             in
          FStar_Syntax_Subst.subst vs t
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universe Prims.list * FStar_Syntax_Syntax.term)
  =
  fun uu___95_1296  ->
    match uu___95_1296 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1310  -> new_u_univ ()))
           in
        let _0_211 = inst_tscheme_with (us, t) us'  in (us', _0_211)
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1321 = inst_tscheme t  in
      match uu____1321 with
      | (us,t) ->
          let _0_212 = FStar_Syntax_Subst.set_use_range r t  in (us, _0_212)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1339  ->
          match uu____1339 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if (FStar_List.length insts) <> (FStar_List.length univs)
                    then
                      failwith
                        (let _0_216 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs)
                            in
                         let _0_215 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let _0_214 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let _0_213 = FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           _0_216 _0_215 _0_214 _0_213)
                    else ();
                    inst_tscheme_with
                      ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                        t) insts)
               | uu____1359 ->
                   failwith
                     (let _0_217 =
                        FStar_Syntax_Print.lid_to_string
                          ed.FStar_Syntax_Syntax.mname
                         in
                      FStar_Util.format1
                        "Unexpected use of an uninstantiated effect: %s\n"
                        _0_217))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1363 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1367 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1371 -> false
  
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
           let cur =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l =
             match (c, l) with
             | ([],uu____1397) -> Maybe
             | (uu____1401,[]) -> No
             | (hd::tl,hd'::tl') when
                 hd.FStar_Ident.idText = hd'.FStar_Ident.idText -> aux tl tl'
             | uu____1413 -> No  in
           aux cur lns)
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
          let uu____1465 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1465 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___96_1482  ->
                   match uu___96_1482 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then Some (FStar_Util.Inl (inst_tscheme t))
                       else None
                   | Binding_sig
                       (uu____1521,FStar_Syntax_Syntax.Sig_bundle
                        (ses,uu____1523,uu____1524,uu____1525))
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1535 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1535
                            then cache (FStar_Util.Inr (se, None))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1555 ->
                             Some t
                         | uu____1562 -> cache t  in
                       let uu____1563 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1563
                       then maybe_cache (FStar_Util.Inr (s, None))
                       else None
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1592 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1592
                       then Some (FStar_Util.Inr (s, (Some us)))
                       else None
                   | uu____1623 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1657 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____1657
         then
           let uu____1666 = find_in_sigtab env lid  in
           match uu____1666 with
           | Some se -> Some (FStar_Util.Inr (se, None))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1717,uu____1718,uu____1719)
          -> add_sigelts env ses
      | uu____1726 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se with
            | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1732) ->
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
            | uu____1736 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs = FStar_Syntax_Syntax.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____1790)::tl -> aux out tl
      | (Binding_lid (_,(_,t)))::tl|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl ->
          let _0_219 =
            let _0_218 = FStar_Syntax_Free.uvars t  in ext out _0_218  in
          aux _0_219 tl
      | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst _)::tl|(Binding_univ _)::tl -> aux out tl
      | (Binding_lid (_,(_,t)))::tl|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl ->
          let _0_221 =
            let _0_220 = FStar_Syntax_Free.univs t  in ext out _0_220  in
          aux _0_221 tl
      | (Binding_sig uu____1857)::uu____1858 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____1895)::tl -> aux out tl
      | (Binding_univ uname)::tl ->
          let _0_222 = FStar_Util.set_add uname out  in aux _0_222 tl
      | (Binding_lid (_,(_,t)))::tl|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl ->
          let _0_224 =
            let _0_223 = FStar_Syntax_Free.univnames t  in ext out _0_223  in
          aux _0_224 tl
      | (Binding_sig uu____1917)::uu____1918 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___97_1934  ->
            match uu___97_1934 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let _0_226 =
      let _0_225 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right _0_225
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right _0_226 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let t_binders :
  env -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list =
  fun env  ->
    let _0_227 = all_binders env  in
    FStar_All.pipe_right _0_227
      (FStar_List.filter
         (fun uu____1965  ->
            match uu____1965 with
            | (x,uu____1969) ->
                let uu____1970 =
                  (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                   in
                (match uu____1970 with
                 | FStar_Syntax_Syntax.Tm_type uu____1971 -> true
                 | uu____1972 -> false)))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a  -> f a e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___98_2011  ->
             match uu___98_2011 with
             | Binding_sig (lids,uu____2015) -> FStar_List.append lids keys
             | uu____2018 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____2020  ->
         fun v  ->
           fun keys  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)
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
        (fun uu___99_2035  ->
           match uu___99_2035 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some (id.FStar_Syntax_Syntax.sort)
           | uu____2042 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2057,lb::[]),uu____2059,uu____2060,uu____2061,uu____2062)
          ->
          Some
            (inst_tscheme
               ((lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp)))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2078,lbs),uu____2080,uu____2081,uu____2082,uu____2083) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2101 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2106 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____2106
                   then
                     Some
                       (inst_tscheme
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)))
                   else None)
      | uu____2118 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____2131) ->
        Some
          (inst_tscheme
             (let _0_228 =
                FStar_Syntax_Util.maybe_tot_arrow
                  ne.FStar_Syntax_Syntax.binders
                  ne.FStar_Syntax_Syntax.signature
                 in
              ((ne.FStar_Syntax_Syntax.univs), _0_228)))
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2137,uu____2138,uu____2139,uu____2140) ->
        Some
          (inst_tscheme
             (let _0_229 =
                FStar_Syntax_Util.maybe_tot_arrow binders
                  FStar_Syntax_Syntax.teff
                 in
              (us, _0_229)))
    | uu____2147 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu___100_2174 =
        match uu___100_2174 with
        | FStar_Util.Inl t -> Some t
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_datacon
             (uu____2195,uvs,t,uu____2198,uu____2199,uu____2200,uu____2201,uu____2202),None
             )
            -> Some (inst_tscheme (uvs, t))
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t,qs,uu____2219),None
             )
            ->
            let uu____2228 = let _0_230 = in_cur_mod env l  in _0_230 = Yes
               in
            if uu____2228
            then
              let uu____2232 =
                (FStar_All.pipe_right qs
                   (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                  || env.is_iface
                 in
              (if uu____2232 then Some (inst_tscheme (uvs, t)) else None)
            else Some (inst_tscheme (uvs, t))
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,uvs,tps,k,uu____2249,uu____2250,uu____2251,uu____2252),None
             )
            ->
            (match tps with
             | [] ->
                 let _0_232 = inst_tscheme (uvs, k)  in
                 FStar_All.pipe_left (fun _0_231  -> Some _0_231) _0_232
             | uu____2277 ->
                 let _0_236 =
                   inst_tscheme
                     (let _0_235 =
                        let _0_234 = FStar_Syntax_Syntax.mk_Total k  in
                        FStar_Syntax_Util.flat_arrow tps _0_234  in
                      (uvs, _0_235))
                    in
                 FStar_All.pipe_left (fun _0_233  -> Some _0_233) _0_236)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,uvs,tps,k,uu____2291,uu____2292,uu____2293,uu____2294),Some
             us)
            ->
            (match tps with
             | [] ->
                 let _0_239 =
                   let _0_238 = inst_tscheme_with (uvs, k) us  in
                   (us, _0_238)  in
                 FStar_All.pipe_left (fun _0_237  -> Some _0_237) _0_239
             | uu____2320 ->
                 let _0_245 =
                   let _0_244 =
                     let _0_243 =
                       let _0_242 =
                         let _0_241 = FStar_Syntax_Syntax.mk_Total k  in
                         FStar_Syntax_Util.flat_arrow tps _0_241  in
                       (uvs, _0_242)  in
                     inst_tscheme_with _0_243 us  in
                   (us, _0_244)  in
                 FStar_All.pipe_left (fun _0_240  -> Some _0_240) _0_245)
        | FStar_Util.Inr se ->
            (match se with
             | (FStar_Syntax_Syntax.Sig_let uu____2342,None ) ->
                 lookup_type_of_let (Prims.fst se) lid
             | uu____2353 -> effect_signature (Prims.fst se))
         in
      let uu____2358 =
        let _0_246 = lookup_qname env lid  in
        FStar_Util.bind_opt _0_246 mapper  in
      match uu____2358 with
      | Some (us,t) ->
          Some
            (us,
              (let uu___114_2386 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___114_2386.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.tk =
                   (uu___114_2386.FStar_Syntax_Syntax.tk);
                 FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.vars =
                   (uu___114_2386.FStar_Syntax_Syntax.vars)
               }))
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2403 = lookup_qname env l  in
      match uu____2403 with | None  -> false | Some uu____2419 -> true
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun bv  ->
      let uu____2440 = try_lookup_bv env bv  in
      match uu____2440 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_248 = variable_not_found bv  in
                let _0_247 = FStar_Syntax_Syntax.range_of_bv bv  in
                (_0_248, _0_247)))
      | Some t ->
          let _0_249 = FStar_Syntax_Syntax.range_of_bv bv  in
          FStar_Syntax_Subst.set_use_range _0_249 t
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2460 = try_lookup_lid_aux env l  in
      match uu____2460 with
      | None  -> None
      | Some (us,t) ->
          Some
            (let _0_250 =
               FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l)
                 t
                in
             (us, _0_250))
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun l  ->
      let uu____2495 = try_lookup_lid env l  in
      match uu____2495 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_251 = name_not_found "lookup_lid" l  in
                (_0_251, (FStar_Ident.range_of_lid l))))
      | Some (us,t) -> (us, t)
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_2516  ->
              match uu___101_2516 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2518 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2529 = lookup_qname env lid  in
      match uu____2529 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2542,uvs,t,q,uu____2546),None ))
          ->
          Some
            (let _0_253 =
               let _0_252 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid lid) t
                  in
               (uvs, _0_252)  in
             (_0_253, q))
      | uu____2570 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2590 = lookup_qname env lid  in
      match uu____2590 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2601,uvs,t,uu____2604,uu____2605),None ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2621 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_254 = name_not_found "lookup_val_decl" lid  in
                (_0_254, (FStar_Ident.range_of_lid lid))))
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2640 = lookup_qname env lid  in
      match uu____2640 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2651,uvs,t,uu____2654,uu____2655,uu____2656,uu____2657,uu____2658),None
           ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2676 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_255 = name_not_found "lookup_datacon" lid  in
                (_0_255, (FStar_Ident.range_of_lid lid))))
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____2696 = lookup_qname env lid  in
      match uu____2696 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2708,uu____2709,uu____2710,uu____2711,uu____2712,dcs,uu____2714,uu____2715),uu____2716))
          -> (true, dcs)
      | uu____2738 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____2754 = lookup_qname env lid  in
      match uu____2754 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2763,uu____2764,uu____2765,l,uu____2767,uu____2768,uu____2769,uu____2770),uu____2771))
          -> l
      | uu____2790 ->
          failwith
            (let _0_256 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format1 "Not a datacon: %s" _0_256)
  
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
        let uu____2822 = lookup_qname env lid  in
        match uu____2822 with
        | Some (FStar_Util.Inr (se,None )) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____2851,lbs),uu____2853,uu____2854,quals,uu____2856)
                 when visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____2873 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____2873
                      then
                        Some
                          (let _0_258 =
                             let _0_257 =
                               FStar_Syntax_Util.unascribe
                                 lb.FStar_Syntax_Syntax.lbdef
                                in
                             FStar_Syntax_Subst.set_use_range
                               (FStar_Ident.range_of_lid lid) _0_257
                              in
                           ((lb.FStar_Syntax_Syntax.lbunivs), _0_258))
                      else None)
             | uu____2886 -> None)
        | uu____2889 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____2908 = lookup_qname env ftv  in
      match uu____2908 with
      | Some (FStar_Util.Inr (se,None )) ->
          let uu____2932 = effect_signature se  in
          (match uu____2932 with
           | None  -> None
           | Some (uu____2939,t) ->
               Some
                 (FStar_Syntax_Subst.set_use_range
                    (FStar_Ident.range_of_lid ftv) t))
      | uu____2943 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____2958 = try_lookup_effect_lid env ftv  in
      match uu____2958 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_259 = name_not_found "lookup_effect_lid" ftv  in
                (_0_259, (FStar_Ident.range_of_lid ftv))))
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
        let uu____2973 = lookup_qname env lid0  in
        match uu____2973 with
        | Some (FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_effect_abbrev
             (lid,univs,binders,c,quals,uu____2990,uu____2991),None ))
            ->
            let lid =
              let _0_260 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid _0_260  in
            let uu____3010 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_3012  ->
                      match uu___102_3012 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3013 -> false))
               in
            if uu____3010
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   if
                     (FStar_Ident.lid_equals lid
                        FStar_Syntax_Const.effect_Lemma_lid)
                       &&
                       ((FStar_List.length univ_insts) =
                          (Prims.parse_int "1"))
                   then
                     FStar_List.append univ_insts
                       [FStar_Syntax_Syntax.U_zero]
                   else
                     failwith
                       (let _0_262 = FStar_Syntax_Print.lid_to_string lid  in
                        let _0_261 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          _0_262 _0_261)
                  in
               match (binders, univs) with
               | ([],uu____3034) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3043,uu____3044::uu____3045::uu____3046) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   failwith
                     (let _0_264 = FStar_Syntax_Print.lid_to_string lid  in
                      let _0_263 =
                        FStar_All.pipe_left FStar_Util.string_of_int
                          (FStar_List.length univs)
                         in
                      FStar_Util.format2
                        "Unexpected effect abbreviation %s; polymorphic in %s universes"
                        _0_264 _0_263)
               | uu____3054 ->
                   let t =
                     let _0_266 =
                       let _0_265 = FStar_Syntax_Util.arrow binders c  in
                       (univs, _0_265)  in
                     inst_tscheme_with _0_266 insts  in
                   let t =
                     FStar_Syntax_Subst.set_use_range
                       (FStar_Ident.range_of_lid lid) t
                      in
                   let uu____3059 =
                     (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                      in
                   (match uu____3059 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                        Some (binders, c)
                    | uu____3087 -> failwith "Impossible"))
        | uu____3091 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find l =
        let uu____3115 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l  in
        match uu____3115 with
        | None  -> None
        | Some (uu____3122,c) ->
            let l = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3127 = find l  in
            (match uu____3127 with | None  -> Some l | Some l' -> Some l')
         in
      let res =
        let uu____3132 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3132 with
        | Some l -> l
        | None  ->
            let uu____3135 = find l  in
            (match uu____3135 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l = norm_eff_name env l  in
      let uu____3147 = lookup_qname env l  in
      match uu____3147 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____3158),uu____3159)) ->
          ne.FStar_Syntax_Syntax.qualifiers
      | uu____3174 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3195 =
          failwith
            (let _0_268 = FStar_Util.string_of_int i  in
             let _0_267 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Impossible: projecting field #%s from constructor %s is undefined"
               _0_268 _0_267)
           in
        let uu____3196 = lookup_datacon env lid  in
        match uu____3196 with
        | (uu____3199,t) ->
            let uu____3201 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            (match uu____3201 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3203) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let _0_269 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right _0_269 Prims.fst)
             | uu____3226 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3233 = lookup_qname env l  in
      match uu____3233 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____3242,uu____3243,uu____3244,quals,uu____3246),uu____3247))
          ->
          FStar_Util.for_some
            (fun uu___103_3264  ->
               match uu___103_3264 with
               | FStar_Syntax_Syntax.Projector uu____3265 -> true
               | uu____3268 -> false) quals
      | uu____3269 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3284 = lookup_qname env lid  in
      match uu____3284 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____3293,uu____3294,uu____3295,uu____3296,uu____3297,uu____3298,uu____3299,uu____3300),uu____3301))
          -> true
      | uu____3320 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3335 = lookup_qname env lid  in
      match uu____3335 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3344,uu____3345,uu____3346,uu____3347,uu____3348,uu____3349,tags,uu____3351),uu____3352))
          ->
          FStar_Util.for_some
            (fun uu___104_3373  ->
               match uu___104_3373 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3376 -> false) tags
      | uu____3377 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3392 = lookup_qname env lid  in
      match uu____3392 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_let
           (uu____3401,uu____3402,uu____3403,tags,uu____3405),uu____3406))
          ->
          FStar_Util.for_some
            (fun uu___105_3427  ->
               match uu___105_3427 with
               | FStar_Syntax_Syntax.Action uu____3428 -> true
               | uu____3429 -> false) tags
      | uu____3430 -> false
  
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
    fun head  ->
      let uu____3447 =
        (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n  in
      match uu____3447 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3449 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper uu___106_3467 =
        match uu___106_3467 with
        | FStar_Util.Inl uu____3476 -> Some false
        | FStar_Util.Inr (se,uu____3485) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____3494,uu____3495,uu____3496,qs,uu____3498) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____3501 -> Some true
             | uu____3513 -> Some false)
         in
      let uu____3514 =
        let _0_270 = lookup_qname env lid  in
        FStar_Util.bind_opt _0_270 mapper  in
      match uu____3514 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____3530 = lookup_qname env lid  in
      match uu____3530 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3539,uu____3540,tps,uu____3542,uu____3543,uu____3544,uu____3545,uu____3546),uu____3547))
          -> FStar_List.length tps
      | uu____3571 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_271 = name_not_found "num_inductive_ty_params" lid  in
                (_0_271, (FStar_Ident.range_of_lid lid))))
  
let comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (Some u)
        | FStar_Syntax_Syntax.GTotal (t,None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (Some u)
        | uu____3601 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____3609 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.comp_typ_name
         in
      match uu____3609 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____3619 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____3619 with
           | (binders,cdef) ->
               (if
                  (FStar_List.length binders) <>
                    (FStar_List.length c.FStar_Syntax_Syntax.effect_args)
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_275 =
                          let _0_274 =
                            FStar_Util.string_of_int
                              (FStar_List.length binders)
                             in
                          let _0_273 =
                            FStar_Util.string_of_int
                              (FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                             in
                          let _0_272 =
                            FStar_Syntax_Print.comp_to_string
                              (FStar_Syntax_Syntax.mk_Comp c)
                             in
                          FStar_Util.format3
                            "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                            _0_274 _0_273 _0_272
                           in
                        (_0_275, (comp.FStar_Syntax_Syntax.pos))))
                else ();
                (let inst =
                   FStar_List.map2
                     (fun uu____3656  ->
                        fun uu____3657  ->
                          match (uu____3656, uu____3657) with
                          | ((x,uu____3671),(t,uu____3673)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders
                     c.FStar_Syntax_Syntax.effect_args
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef  in
                 let c =
                   let _0_276 =
                     let uu___115_3688 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_typ_name =
                         (uu___115_3688.FStar_Syntax_Syntax.comp_typ_name);
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___115_3688.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___115_3688.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right _0_276 FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c)))
  
let result_typ : env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun comp  ->
      match comp.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
      | uu____3708 ->
          let ct = unfold_effect_abbrev env comp  in
          if
            (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Tot_lid)
              ||
              (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
                 FStar_Syntax_Const.effect_GTot_lid)
          then
            let _0_277 = FStar_List.hd ct.FStar_Syntax_Syntax.effect_args  in
            FStar_All.pipe_left Prims.fst _0_277
          else
            (let _0_278 =
               FStar_List.nth ct.FStar_Syntax_Syntax.effect_args
                 ((FStar_List.length ct.FStar_Syntax_Syntax.effect_args) -
                    (Prims.parse_int "2"))
                in
             FStar_All.pipe_left Prims.fst _0_278)
  
let rec non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3748 = (FStar_Syntax_Util.unrefine t).FStar_Syntax_Syntax.n
         in
      match uu____3748 with
      | FStar_Syntax_Syntax.Tm_type uu____3749 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
      | FStar_Syntax_Syntax.Tm_app (head,uu____3752) ->
          non_informative env head
      | FStar_Syntax_Syntax.Tm_uinst (t,uu____3768) -> non_informative env t
      | FStar_Syntax_Syntax.Tm_arrow (uu____3773,c) ->
          (FStar_Syntax_Util.is_tot_or_gtot_comp c) &&
            (let _0_279 = result_typ env c  in non_informative env _0_279)
      | uu____3785 -> false
  
let comp_as_normal_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> normal_comp_typ =
  fun env  ->
    fun c  ->
      let ct = unfold_effect_abbrev env c  in
      let rec aux uu___107_3809 =
        match uu___107_3809 with
        | [] ->
            failwith
              (FStar_Util.format1
                 "Expected at least two arguments to comp_typ (%s)"
                 (FStar_Ident.text_of_lid
                    ct.FStar_Syntax_Syntax.comp_typ_name))
        | res::[] ->
            failwith
              (let _0_280 = FStar_Syntax_Print.term_to_string (Prims.fst res)
                  in
               FStar_Util.format2
                 "Expected at least two arguments to comp_typ (%s) got %s"
                 (FStar_Ident.text_of_lid
                    ct.FStar_Syntax_Syntax.comp_typ_name) _0_280)
        | res::wp::[] -> ([], res, wp)
        | hd::rest ->
            let uu____3882 = aux rest  in
            (match uu____3882 with | (i,res,wp) -> ((hd :: i), res, wp))
         in
      let uu____3929 = aux ct.FStar_Syntax_Syntax.effect_args  in
      match uu____3929 with
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
        let _0_282 =
          let _0_281 = FStar_List.hd ct0.FStar_Syntax_Syntax.effect_args  in
          FStar_All.pipe_left Prims.fst _0_281  in
        {
          FStar_Syntax_Syntax.lcomp_name =
            (ct0.FStar_Syntax_Syntax.comp_typ_name);
          FStar_Syntax_Syntax.lcomp_univs =
            (ct0.FStar_Syntax_Syntax.comp_univs);
          FStar_Syntax_Syntax.lcomp_indices = [];
          FStar_Syntax_Syntax.lcomp_res_typ = _0_282;
          FStar_Syntax_Syntax.lcomp_cflags = (ct0.FStar_Syntax_Syntax.flags);
          FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____3991  -> c0)
        }
      else
        (let nct = comp_as_normal_comp_typ env c0  in
         {
           FStar_Syntax_Syntax.lcomp_name = (nct.nct_name);
           FStar_Syntax_Syntax.lcomp_univs = (nct.nct_univs);
           FStar_Syntax_Syntax.lcomp_indices = (nct.nct_indices);
           FStar_Syntax_Syntax.lcomp_res_typ = (Prims.fst nct.nct_result);
           FStar_Syntax_Syntax.lcomp_cflags = (nct.nct_flags);
           FStar_Syntax_Syntax.lcomp_as_comp = (fun uu____3996  -> c0)
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
          FStar_Syntax_Syntax.mk_Comp
            (let uu___116_4007 = ct  in
             let _0_284 =
               let _0_283 = FStar_Syntax_Syntax.as_arg t  in [_0_283]  in
             {
               FStar_Syntax_Syntax.comp_typ_name =
                 (uu___116_4007.FStar_Syntax_Syntax.comp_typ_name);
               FStar_Syntax_Syntax.comp_univs =
                 (uu___116_4007.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_args = _0_284;
               FStar_Syntax_Syntax.flags =
                 (uu___116_4007.FStar_Syntax_Syntax.flags)
             })
        else
          (let nct = comp_as_normal_comp_typ env c  in
           let nct =
             let uu___117_4011 = nct  in
             let _0_285 = FStar_Syntax_Syntax.as_arg t  in
             {
               nct_name = (uu___117_4011.nct_name);
               nct_univs = (uu___117_4011.nct_univs);
               nct_indices = (uu___117_4011.nct_indices);
               nct_result = _0_285;
               nct_wp = (uu___117_4011.nct_wp);
               nct_flags = (uu___117_4011.nct_flags)
             }  in
           normal_comp_typ_as_comp env nct)
  
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
            let uv =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv, uv)
        | uu____4056 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let _0_286 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders _0_286  in
            let uv =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let _0_287 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (_0_287, uv)
  
let new_uvar_for_env :
  env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun k  ->
      let bs =
        let uu____4114 =
          (FStar_Options.full_context_dependency ()) ||
            (let _0_288 = current_module env  in
             FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_288)
           in
        if uu____4114 then all_binders env else t_binders env  in
      let _0_289 = get_range env  in new_uvar _0_289 bs k
  
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
      let uu____4132 = effect_decl_opt env l  in
      match uu____4132 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_290 = name_not_found "get_effect_decl" l  in
                (_0_290, (FStar_Ident.range_of_lid l))))
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
        then let id x = x  in (l1, id, id)
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
            (let lift_gtot nct =
               let uu___118_4169 = nct  in
               {
                 nct_name = FStar_Syntax_Const.effect_GTot_lid;
                 nct_univs = (uu___118_4169.nct_univs);
                 nct_indices = (uu___118_4169.nct_indices);
                 nct_result = (uu___118_4169.nct_result);
                 nct_wp = (uu___118_4169.nct_wp);
                 nct_flags = (uu___118_4169.nct_flags)
               }  in
             (FStar_Syntax_Const.effect_GTot_lid, lift_gtot, lift_gtot))
          else
            (let uu____4175 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4199  ->
                       match uu____4199 with
                       | (m1,m2,uu____4207,uu____4208,uu____4209) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____4175 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      (let _0_293 =
                         let _0_292 = FStar_Syntax_Print.lid_to_string l1  in
                         let _0_291 = FStar_Syntax_Print.lid_to_string l2  in
                         FStar_Util.format2
                           "Effects %s and %s cannot be composed" _0_292
                           _0_291
                          in
                       (_0_293, (env.range))))
             | Some (uu____4221,uu____4222,m3,j1,j2) -> (m3, j1, j2))
  
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
                   let uu___119_4248 = nct  in
                   {
                     nct_name = l2;
                     nct_univs = (uu___119_4248.nct_univs);
                     nct_indices = (uu___119_4248.nct_indices);
                     nct_result = (uu___119_4248.nct_result);
                     nct_wp = (uu___119_4248.nct_wp);
                     nct_flags = (uu___119_4248.nct_flags)
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
        let uu____4268 =
          FStar_All.pipe_right decls
            (FStar_Util.find_opt
               (fun d  ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
           in
        match uu____4268 with
        | None  ->
            failwith
              (FStar_Util.format1
                 "Impossible: declaration for monad %s not found"
                 m.FStar_Ident.str)
        | Some md ->
            let uu____4282 =
              inst_tscheme
                ((md.FStar_Syntax_Syntax.univs),
                  (md.FStar_Syntax_Syntax.signature))
               in
            (match uu____4282 with
             | (uu____4289,s) ->
                 let s = FStar_Syntax_Subst.compress s  in
                 (match ((md.FStar_Syntax_Syntax.binders),
                          (s.FStar_Syntax_Syntax.n))
                  with
                  | ([],FStar_Syntax_Syntax.Tm_arrow
                     ((a,uu____4297)::(wp,uu____4299)::[],c)) when
                      FStar_Syntax_Syntax.is_teff (result_typ env c) ->
                      (a, (wp.FStar_Syntax_Syntax.sort))
                  | uu____4321 -> failwith "Impossible"))
  
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
              (let eff_name = norm_eff_name env eff_name  in
               let ed = get_effect_decl env eff_name  in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp
                  in
               let null_wp_res =
                 let _0_296 = get_range env  in
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (let _0_295 =
                          let _0_294 = FStar_Syntax_Syntax.as_arg res_t  in
                          [_0_294]  in
                        (null_wp, _0_295)))) None _0_296
                  in
               FStar_Syntax_Syntax.mk_Comp
                 (let _0_300 =
                    let _0_299 = FStar_Syntax_Syntax.as_arg res_t  in
                    let _0_298 =
                      let _0_297 = FStar_Syntax_Syntax.as_arg null_wp_res  in
                      [_0_297]  in
                    _0_299 :: _0_298  in
                  {
                    FStar_Syntax_Syntax.comp_typ_name = eff_name;
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_args = _0_300;
                    FStar_Syntax_Syntax.flags = []
                  }))
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest -> let _0_301 = push x rest  in local :: _0_301  in
      let uu___120_4389 = env  in
      let _0_302 = push s env.gamma  in
      {
        solver = (uu___120_4389.solver);
        range = (uu___120_4389.range);
        curmodule = (uu___120_4389.curmodule);
        gamma = _0_302;
        gamma_cache = (uu___120_4389.gamma_cache);
        modules = (uu___120_4389.modules);
        expected_typ = (uu___120_4389.expected_typ);
        sigtab = (uu___120_4389.sigtab);
        is_pattern = (uu___120_4389.is_pattern);
        instantiate_imp = (uu___120_4389.instantiate_imp);
        effects = (uu___120_4389.effects);
        generalize = (uu___120_4389.generalize);
        letrecs = (uu___120_4389.letrecs);
        top_level = (uu___120_4389.top_level);
        check_uvars = (uu___120_4389.check_uvars);
        use_eq = (uu___120_4389.use_eq);
        is_iface = (uu___120_4389.is_iface);
        admit = (uu___120_4389.admit);
        lax = (uu___120_4389.lax);
        lax_universes = (uu___120_4389.lax_universes);
        type_of = (uu___120_4389.type_of);
        universe_of = (uu___120_4389.universe_of);
        use_bv_sorts = (uu___120_4389.use_bv_sorts);
        qname_and_index = (uu___120_4389.qname_and_index)
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
      let uu___121_4413 = env  in
      {
        solver = (uu___121_4413.solver);
        range = (uu___121_4413.range);
        curmodule = (uu___121_4413.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___121_4413.gamma_cache);
        modules = (uu___121_4413.modules);
        expected_typ = (uu___121_4413.expected_typ);
        sigtab = (uu___121_4413.sigtab);
        is_pattern = (uu___121_4413.is_pattern);
        instantiate_imp = (uu___121_4413.instantiate_imp);
        effects = (uu___121_4413.effects);
        generalize = (uu___121_4413.generalize);
        letrecs = (uu___121_4413.letrecs);
        top_level = (uu___121_4413.top_level);
        check_uvars = (uu___121_4413.check_uvars);
        use_eq = (uu___121_4413.use_eq);
        is_iface = (uu___121_4413.is_iface);
        admit = (uu___121_4413.admit);
        lax = (uu___121_4413.lax);
        lax_universes = (uu___121_4413.lax_universes);
        type_of = (uu___121_4413.type_of);
        universe_of = (uu___121_4413.universe_of);
        use_bv_sorts = (uu___121_4413.use_bv_sorts);
        qname_and_index = (uu___121_4413.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env  ->
           fun uu____4429  ->
             match uu____4429 with | (x,uu____4433) -> push_bv env x) env bs
  
let binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x ->
          let x =
            let uu___122_4453 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_4453.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_4453.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (Prims.snd t)
            }  in
          Binding_var x
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
      (let uu___123_4483 = env  in
       {
         solver = (uu___123_4483.solver);
         range = (uu___123_4483.range);
         curmodule = (uu___123_4483.curmodule);
         gamma = [];
         gamma_cache = (uu___123_4483.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___123_4483.sigtab);
         is_pattern = (uu___123_4483.is_pattern);
         instantiate_imp = (uu___123_4483.instantiate_imp);
         effects = (uu___123_4483.effects);
         generalize = (uu___123_4483.generalize);
         letrecs = (uu___123_4483.letrecs);
         top_level = (uu___123_4483.top_level);
         check_uvars = (uu___123_4483.check_uvars);
         use_eq = (uu___123_4483.use_eq);
         is_iface = (uu___123_4483.is_iface);
         admit = (uu___123_4483.admit);
         lax = (uu___123_4483.lax);
         lax_universes = (uu___123_4483.lax_universes);
         type_of = (uu___123_4483.type_of);
         universe_of = (uu___123_4483.universe_of);
         use_bv_sorts = (uu___123_4483.use_bv_sorts);
         qname_and_index = (uu___123_4483.qname_and_index)
       })
  
let push_univ_vars : env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env  -> fun x  -> push_local_binding env (Binding_univ x)) env
        xs
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___124_4498 = env  in
      {
        solver = (uu___124_4498.solver);
        range = (uu___124_4498.range);
        curmodule = (uu___124_4498.curmodule);
        gamma = (uu___124_4498.gamma);
        gamma_cache = (uu___124_4498.gamma_cache);
        modules = (uu___124_4498.modules);
        expected_typ = (Some t);
        sigtab = (uu___124_4498.sigtab);
        is_pattern = (uu___124_4498.is_pattern);
        instantiate_imp = (uu___124_4498.instantiate_imp);
        effects = (uu___124_4498.effects);
        generalize = (uu___124_4498.generalize);
        letrecs = (uu___124_4498.letrecs);
        top_level = (uu___124_4498.top_level);
        check_uvars = (uu___124_4498.check_uvars);
        use_eq = false;
        is_iface = (uu___124_4498.is_iface);
        admit = (uu___124_4498.admit);
        lax = (uu___124_4498.lax);
        lax_universes = (uu___124_4498.lax_universes);
        type_of = (uu___124_4498.type_of);
        universe_of = (uu___124_4498.universe_of);
        use_bv_sorts = (uu___124_4498.use_bv_sorts);
        qname_and_index = (uu___124_4498.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let _0_303 = expected_typ env_  in
    ((let uu___125_4515 = env_  in
      {
        solver = (uu___125_4515.solver);
        range = (uu___125_4515.range);
        curmodule = (uu___125_4515.curmodule);
        gamma = (uu___125_4515.gamma);
        gamma_cache = (uu___125_4515.gamma_cache);
        modules = (uu___125_4515.modules);
        expected_typ = None;
        sigtab = (uu___125_4515.sigtab);
        is_pattern = (uu___125_4515.is_pattern);
        instantiate_imp = (uu___125_4515.instantiate_imp);
        effects = (uu___125_4515.effects);
        generalize = (uu___125_4515.generalize);
        letrecs = (uu___125_4515.letrecs);
        top_level = (uu___125_4515.top_level);
        check_uvars = (uu___125_4515.check_uvars);
        use_eq = false;
        is_iface = (uu___125_4515.is_iface);
        admit = (uu___125_4515.admit);
        lax = (uu___125_4515.lax);
        lax_universes = (uu___125_4515.lax_universes);
        type_of = (uu___125_4515.type_of);
        universe_of = (uu___125_4515.universe_of);
        use_bv_sorts = (uu___125_4515.use_bv_sorts);
        qname_and_index = (uu___125_4515.qname_and_index)
      }), _0_303)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let _0_304 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___108_4530  ->
                    match uu___108_4530 with
                    | Binding_sig (uu____4532,se) -> [se]
                    | uu____4536 -> []))
             in
          FStar_All.pipe_right _0_304 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___126_4539 = env  in
       {
         solver = (uu___126_4539.solver);
         range = (uu___126_4539.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___126_4539.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___126_4539.expected_typ);
         sigtab = (uu___126_4539.sigtab);
         is_pattern = (uu___126_4539.is_pattern);
         instantiate_imp = (uu___126_4539.instantiate_imp);
         effects = (uu___126_4539.effects);
         generalize = (uu___126_4539.generalize);
         letrecs = (uu___126_4539.letrecs);
         top_level = (uu___126_4539.top_level);
         check_uvars = (uu___126_4539.check_uvars);
         use_eq = (uu___126_4539.use_eq);
         is_iface = (uu___126_4539.is_iface);
         admit = (uu___126_4539.admit);
         lax = (uu___126_4539.lax);
         lax_universes = (uu___126_4539.lax_universes);
         type_of = (uu___126_4539.type_of);
         universe_of = (uu___126_4539.universe_of);
         use_bv_sorts = (uu___126_4539.use_bv_sorts);
         qname_and_index = (uu___126_4539.qname_and_index)
       })
  
let dummy_solver : solver_t =
  {
    init = (fun uu____4540  -> ());
    push = (fun uu____4541  -> ());
    pop = (fun uu____4542  -> ());
    mark = (fun uu____4543  -> ());
    reset_mark = (fun uu____4544  -> ());
    commit_mark = (fun uu____4545  -> ());
    encode_modul = (fun uu____4546  -> fun uu____4547  -> ());
    encode_sig = (fun uu____4548  -> fun uu____4549  -> ());
    solve = (fun uu____4550  -> fun uu____4551  -> fun uu____4552  -> ());
    is_trivial = (fun uu____4556  -> fun uu____4557  -> false);
    finish = (fun uu____4558  -> ());
    refresh = (fun uu____4559  -> ())
  } 