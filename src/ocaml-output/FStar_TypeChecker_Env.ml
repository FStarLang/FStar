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
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      Prims.option
    }
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
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                Prims.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
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
  preprocess: env -> goal -> (env * goal) Prims.list ;
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
      | uu____839 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____849 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____857 =
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
          let uu____896 = new_gamma_cache ()  in
          let uu____898 = new_sigtab ()  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____896;
            modules = [];
            expected_typ = None;
            sigtab = uu____898;
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
  fun uu____938  ->
    let uu____939 = FStar_ST.read query_indices  in
    match uu____939 with
    | [] -> failwith "Empty query indices!"
    | uu____953 ->
        let uu____958 =
          let uu____963 =
            let uu____967 = FStar_ST.read query_indices  in
            FStar_List.hd uu____967  in
          let uu____981 = FStar_ST.read query_indices  in uu____963 ::
            uu____981
           in
        FStar_ST.write query_indices uu____958
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____1003  ->
    let uu____1004 = FStar_ST.read query_indices  in
    match uu____1004 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____1040  ->
    match uu____1040 with
    | (l,n1) ->
        let uu____1045 = FStar_ST.read query_indices  in
        (match uu____1045 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1079 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1089  ->
    let uu____1090 = FStar_ST.read query_indices  in FStar_List.hd uu____1090
  
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1106  ->
    let uu____1107 = FStar_ST.read query_indices  in
    match uu____1107 with
    | hd1::uu____1119::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1146 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____1160 =
       let uu____1162 = FStar_ST.read stack  in env :: uu____1162  in
     FStar_ST.write stack uu____1160);
    (let uu___110_1170 = env  in
     let uu____1171 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____1173 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___110_1170.solver);
       range = (uu___110_1170.range);
       curmodule = (uu___110_1170.curmodule);
       gamma = (uu___110_1170.gamma);
       gamma_cache = uu____1171;
       modules = (uu___110_1170.modules);
       expected_typ = (uu___110_1170.expected_typ);
       sigtab = uu____1173;
       is_pattern = (uu___110_1170.is_pattern);
       instantiate_imp = (uu___110_1170.instantiate_imp);
       effects = (uu___110_1170.effects);
       generalize = (uu___110_1170.generalize);
       letrecs = (uu___110_1170.letrecs);
       top_level = (uu___110_1170.top_level);
       check_uvars = (uu___110_1170.check_uvars);
       use_eq = (uu___110_1170.use_eq);
       is_iface = (uu___110_1170.is_iface);
       admit = (uu___110_1170.admit);
       lax = (uu___110_1170.lax);
       lax_universes = (uu___110_1170.lax_universes);
       type_of = (uu___110_1170.type_of);
       universe_of = (uu___110_1170.universe_of);
       use_bv_sorts = (uu___110_1170.use_bv_sorts);
       qname_and_index = (uu___110_1170.qname_and_index)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1177  ->
    let uu____1178 = FStar_ST.read stack  in
    match uu____1178 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1190 -> failwith "Impossible: Too many pops"
  
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
    (let uu____1222 = pop_stack ()  in ());
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
        let uu____1241 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1253  ->
                  match uu____1253 with
                  | (m,uu____1257) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1241 with
         | None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___111_1262 = env  in
               {
                 solver = (uu___111_1262.solver);
                 range = (uu___111_1262.range);
                 curmodule = (uu___111_1262.curmodule);
                 gamma = (uu___111_1262.gamma);
                 gamma_cache = (uu___111_1262.gamma_cache);
                 modules = (uu___111_1262.modules);
                 expected_typ = (uu___111_1262.expected_typ);
                 sigtab = (uu___111_1262.sigtab);
                 is_pattern = (uu___111_1262.is_pattern);
                 instantiate_imp = (uu___111_1262.instantiate_imp);
                 effects = (uu___111_1262.effects);
                 generalize = (uu___111_1262.generalize);
                 letrecs = (uu___111_1262.letrecs);
                 top_level = (uu___111_1262.top_level);
                 check_uvars = (uu___111_1262.check_uvars);
                 use_eq = (uu___111_1262.use_eq);
                 is_iface = (uu___111_1262.is_iface);
                 admit = (uu___111_1262.admit);
                 lax = (uu___111_1262.lax);
                 lax_universes = (uu___111_1262.lax_universes);
                 type_of = (uu___111_1262.type_of);
                 universe_of = (uu___111_1262.universe_of);
                 use_bv_sorts = (uu___111_1262.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1265,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___112_1271 = env  in
               {
                 solver = (uu___112_1271.solver);
                 range = (uu___112_1271.range);
                 curmodule = (uu___112_1271.curmodule);
                 gamma = (uu___112_1271.gamma);
                 gamma_cache = (uu___112_1271.gamma_cache);
                 modules = (uu___112_1271.modules);
                 expected_typ = (uu___112_1271.expected_typ);
                 sigtab = (uu___112_1271.sigtab);
                 is_pattern = (uu___112_1271.is_pattern);
                 instantiate_imp = (uu___112_1271.instantiate_imp);
                 effects = (uu___112_1271.effects);
                 generalize = (uu___112_1271.generalize);
                 letrecs = (uu___112_1271.letrecs);
                 top_level = (uu___112_1271.top_level);
                 check_uvars = (uu___112_1271.check_uvars);
                 use_eq = (uu___112_1271.use_eq);
                 is_iface = (uu___112_1271.is_iface);
                 admit = (uu___112_1271.admit);
                 lax = (uu___112_1271.lax);
                 lax_universes = (uu___112_1271.lax_universes);
                 type_of = (uu___112_1271.type_of);
                 universe_of = (uu___112_1271.universe_of);
                 use_bv_sorts = (uu___112_1271.use_bv_sorts);
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
        (let uu___113_1287 = e  in
         {
           solver = (uu___113_1287.solver);
           range = r;
           curmodule = (uu___113_1287.curmodule);
           gamma = (uu___113_1287.gamma);
           gamma_cache = (uu___113_1287.gamma_cache);
           modules = (uu___113_1287.modules);
           expected_typ = (uu___113_1287.expected_typ);
           sigtab = (uu___113_1287.sigtab);
           is_pattern = (uu___113_1287.is_pattern);
           instantiate_imp = (uu___113_1287.instantiate_imp);
           effects = (uu___113_1287.effects);
           generalize = (uu___113_1287.generalize);
           letrecs = (uu___113_1287.letrecs);
           top_level = (uu___113_1287.top_level);
           check_uvars = (uu___113_1287.check_uvars);
           use_eq = (uu___113_1287.use_eq);
           is_iface = (uu___113_1287.is_iface);
           admit = (uu___113_1287.admit);
           lax = (uu___113_1287.lax);
           lax_universes = (uu___113_1287.lax_universes);
           type_of = (uu___113_1287.type_of);
           universe_of = (uu___113_1287.universe_of);
           use_bv_sorts = (uu___113_1287.use_bv_sorts);
           qname_and_index = (uu___113_1287.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___114_1304 = env  in
      {
        solver = (uu___114_1304.solver);
        range = (uu___114_1304.range);
        curmodule = lid;
        gamma = (uu___114_1304.gamma);
        gamma_cache = (uu___114_1304.gamma_cache);
        modules = (uu___114_1304.modules);
        expected_typ = (uu___114_1304.expected_typ);
        sigtab = (uu___114_1304.sigtab);
        is_pattern = (uu___114_1304.is_pattern);
        instantiate_imp = (uu___114_1304.instantiate_imp);
        effects = (uu___114_1304.effects);
        generalize = (uu___114_1304.generalize);
        letrecs = (uu___114_1304.letrecs);
        top_level = (uu___114_1304.top_level);
        check_uvars = (uu___114_1304.check_uvars);
        use_eq = (uu___114_1304.use_eq);
        is_iface = (uu___114_1304.is_iface);
        admit = (uu___114_1304.admit);
        lax = (uu___114_1304.lax);
        lax_universes = (uu___114_1304.lax_universes);
        type_of = (uu___114_1304.type_of);
        universe_of = (uu___114_1304.universe_of);
        use_bv_sorts = (uu___114_1304.use_bv_sorts);
        qname_and_index = (uu___114_1304.qname_and_index)
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
  
let name_not_found : FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str 
let variable_not_found : FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1326 = FStar_Syntax_Print.bv_to_string v1  in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1326
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1329  ->
    let uu____1330 = FStar_Unionfind.fresh None  in
    FStar_Syntax_Syntax.U_unif uu____1330
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1353) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____1369 = FStar_Syntax_Subst.subst vs t  in (us, uu____1369)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun uu___98_1374  ->
    match uu___98_1374 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1388  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1398 = inst_tscheme t  in
      match uu____1398 with
      | (us,t1) ->
          let uu____1405 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____1405)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1417  ->
          match uu____1417 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1431 =
                         let uu____1432 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____1435 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____1438 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____1439 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1432 uu____1435 uu____1438 uu____1439
                          in
                       failwith uu____1431)
                    else ();
                    (let uu____1441 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     Prims.snd uu____1441))
               | uu____1445 ->
                   let uu____1446 =
                     let uu____1447 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1447
                      in
                   failwith uu____1446)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1451 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1455 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1459 -> false
  
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
             | ([],uu____1485) -> Maybe
             | (uu____1489,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1501 -> No  in
           aux cur1 lns)
        else No
  
let lookup_qname :
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                    *
                                                                    FStar_Syntax_Syntax.universes
                                                                    Prims.option))
        FStar_Util.either * FStar_Range.range) Prims.option
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
          let uu____1561 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1561 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___99_1582  ->
                   match uu___99_1582 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1605 =
                           let uu____1615 =
                             let uu____1623 = inst_tscheme t  in
                             FStar_Util.Inl uu____1623  in
                           (uu____1615, (FStar_Ident.range_of_lid l))  in
                         Some uu____1605
                       else None
                   | Binding_sig
                       (uu____1657,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1659,uu____1660);
                                     FStar_Syntax_Syntax.sigrng = uu____1661;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1671 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1671
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1698 ->
                             Some t
                         | uu____1704 -> cache t  in
                       let uu____1705 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____1705 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1745 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____1745 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1789 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1831 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____1831
         then
           let uu____1842 = find_in_sigtab env lid  in
           match uu____1842 with
           | Some se ->
               Some
                 ((FStar_Util.Inr (se, None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1908,uu____1909) ->
          add_sigelts env ses
      | uu____1916 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
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
                            ne.FStar_Syntax_Syntax.mname a
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____1925 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Range.range) Prims.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___100_1943  ->
           match uu___100_1943 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____1956 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
        FStar_Range.range) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1977,lb::[]),uu____1979,uu____1980,uu____1981) ->
          let uu____1992 =
            let uu____1997 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp))
               in
            let uu____2003 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname
               in
            (uu____1997, uu____2003)  in
          Some uu____1992
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2010,lbs),uu____2012,uu____2013,uu____2014) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2036 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2043 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____2043
                   then
                     let uu____2049 =
                       let uu____2054 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp))
                          in
                       let uu____2060 = FStar_Syntax_Syntax.range_of_fv fv
                          in
                       (uu____2054, uu____2060)  in
                     Some uu____2049
                   else None)
      | uu____2072 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
      FStar_Range.range) Prims.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2091 =
          let uu____2096 =
            let uu____2099 =
              let uu____2100 =
                let uu____2103 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2103
                 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2100)  in
            inst_tscheme uu____2099  in
          (uu____2096, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____2091
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2117,uu____2118,uu____2119) ->
        let uu____2124 =
          let uu____2129 =
            let uu____2132 =
              let uu____2133 =
                let uu____2136 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders uu____2136  in
              (us, uu____2133)  in
            inst_tscheme uu____2132  in
          (uu____2129, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____2124
    | uu____2147 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) * FStar_Range.range) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2182 =
        match uu____2182 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2232,uvs,t,uu____2235,uu____2236,uu____2237,uu____2238);
                    FStar_Syntax_Syntax.sigrng = uu____2239;_},None
                  )
                 ->
                 let uu____2250 =
                   let uu____2255 = inst_tscheme (uvs, t)  in
                   (uu____2255, rng)  in
                 Some uu____2250
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t,qs);
                    FStar_Syntax_Syntax.sigrng = uu____2268;_},None
                  )
                 ->
                 let uu____2277 =
                   let uu____2278 = in_cur_mod env l  in uu____2278 = Yes  in
                 if uu____2277
                 then
                   let uu____2284 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface
                      in
                   (if uu____2284
                    then
                      let uu____2291 =
                        let uu____2296 = inst_tscheme (uvs, t)  in
                        (uu____2296, rng)  in
                      Some uu____2291
                    else None)
                 else
                   (let uu____2311 =
                      let uu____2316 = inst_tscheme (uvs, t)  in
                      (uu____2316, rng)  in
                    Some uu____2311)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2329,uu____2330,uu____2331);
                    FStar_Syntax_Syntax.sigrng = uu____2332;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2352 =
                        let uu____2357 = inst_tscheme (uvs, k)  in
                        (uu____2357, rng)  in
                      Some uu____2352
                  | uu____2366 ->
                      let uu____2367 =
                        let uu____2372 =
                          let uu____2375 =
                            let uu____2376 =
                              let uu____2379 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____2379  in
                            (uvs, uu____2376)  in
                          inst_tscheme uu____2375  in
                        (uu____2372, rng)  in
                      Some uu____2367)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2394,uu____2395,uu____2396);
                    FStar_Syntax_Syntax.sigrng = uu____2397;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2418 =
                        let uu____2423 = inst_tscheme_with (uvs, k) us  in
                        (uu____2423, rng)  in
                      Some uu____2418
                  | uu____2432 ->
                      let uu____2433 =
                        let uu____2438 =
                          let uu____2441 =
                            let uu____2442 =
                              let uu____2445 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____2445  in
                            (uvs, uu____2442)  in
                          inst_tscheme_with uu____2441 us  in
                        (uu____2438, rng)  in
                      Some uu____2433)
             | FStar_Util.Inr se ->
                 let uu____2465 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2476;
                        FStar_Syntax_Syntax.sigrng = uu____2477;_},None
                      ) -> lookup_type_of_let (Prims.fst se) lid
                   | uu____2487 -> effect_signature (Prims.fst se)  in
                 FStar_All.pipe_right uu____2465
                   (FStar_Util.map_option
                      (fun uu____2510  ->
                         match uu____2510 with | (us_t,rng1) -> (us_t, rng1))))
         in
      let uu____2527 =
        let uu____2533 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____2533 mapper  in
      match uu____2527 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___115_2585 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___115_2585.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___115_2585.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___115_2585.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2606 = lookup_qname env l  in
      match uu____2606 with | None  -> false | Some uu____2626 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____2654 = try_lookup_bv env bv  in
      match uu____2654 with
      | None  ->
          let uu____2662 =
            let uu____2663 =
              let uu____2666 = variable_not_found bv  in (uu____2666, bvr)
               in
            FStar_Errors.Error uu____2663  in
          Prims.raise uu____2662
      | Some (t,r) ->
          let uu____2673 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____2674 = FStar_Range.set_use_range r bvr  in
          (uu____2673, uu____2674)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2686 = try_lookup_lid_aux env l  in
      match uu____2686 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 = FStar_Range.set_use_range r use_range  in
          let uu____2728 =
            let uu____2733 =
              let uu____2736 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____2736)  in
            (uu____2733, r1)  in
          Some uu____2728
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2753 = try_lookup_lid env l  in
      match uu____2753 with
      | None  ->
          (FStar_Util.print1 "got here%s" "\n";
           (let uu____2768 =
              let uu____2769 =
                let uu____2772 = name_not_found l  in
                (uu____2772, (FStar_Ident.range_of_lid l))  in
              FStar_Errors.Error uu____2769  in
            Prims.raise uu____2768))
      | Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___101_2793  ->
              match uu___101_2793 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2795 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2806 = lookup_qname env lid  in
      match uu____2806 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2821,uvs,t,q);
              FStar_Syntax_Syntax.sigrng = uu____2825;_},None
            ),uu____2826)
          ->
          let uu____2851 =
            let uu____2857 =
              let uu____2860 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____2860)  in
            (uu____2857, q)  in
          Some uu____2851
      | uu____2869 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2891 = lookup_qname env lid  in
      match uu____2891 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2904,uvs,t,uu____2907);
              FStar_Syntax_Syntax.sigrng = uu____2908;_},None
            ),uu____2909)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2934 ->
          let uu____2945 =
            let uu____2946 =
              let uu____2949 = name_not_found lid  in
              (uu____2949, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2946  in
          Prims.raise uu____2945
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2960 = lookup_qname env lid  in
      match uu____2960 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____2973,uvs,t,uu____2976,uu____2977,uu____2978,uu____2979);
              FStar_Syntax_Syntax.sigrng = uu____2980;_},None
            ),uu____2981)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3008 ->
          let uu____3019 =
            let uu____3020 =
              let uu____3023 = name_not_found lid  in
              (uu____3023, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3020  in
          Prims.raise uu____3019
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3035 = lookup_qname env lid  in
      match uu____3035 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3049,uu____3050,uu____3051,uu____3052,uu____3053,dcs,uu____3055);
              FStar_Syntax_Syntax.sigrng = uu____3056;_},uu____3057),uu____3058)
          -> (true, dcs)
      | uu____3089 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3107 = lookup_qname env lid  in
      match uu____3107 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3118,uu____3119,uu____3120,l,uu____3122,uu____3123,uu____3124);
              FStar_Syntax_Syntax.sigrng = uu____3125;_},uu____3126),uu____3127)
          -> l
      | uu____3155 ->
          let uu____3166 =
            let uu____3167 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____3167  in
          failwith uu____3166
  
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
        let uu____3191 = lookup_qname env lid  in
        match uu____3191 with
        | Some (FStar_Util.Inr (se,None ),uu____3206) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3232,lbs),uu____3234,quals,uu____3236) when
                 visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____3253 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____3253
                      then
                        let uu____3258 =
                          let uu____3262 =
                            let uu____3263 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef
                               in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3263
                             in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3262)  in
                        Some uu____3258
                      else None)
             | uu____3272 -> None)
        | uu____3275 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3296 = lookup_qname env ftv  in
      match uu____3296 with
      | Some (FStar_Util.Inr (se,None ),uu____3309) ->
          let uu____3332 = effect_signature se  in
          (match uu____3332 with
           | None  -> None
           | Some ((uu____3343,t),r) ->
               let uu____3352 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               Some uu____3352)
      | uu____3353 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____3370 = try_lookup_effect_lid env ftv  in
      match uu____3370 with
      | None  ->
          let uu____3372 =
            let uu____3373 =
              let uu____3376 = name_not_found ftv  in
              (uu____3376, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3373  in
          Prims.raise uu____3372
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
        let uu____3390 = lookup_qname env lid0  in
        match uu____3390 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,quals,uu____3409);
                FStar_Syntax_Syntax.sigrng = uu____3410;_},None
              ),uu____3411)
            ->
            let lid1 =
              let uu____3439 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____3439  in
            let uu____3440 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___102_3442  ->
                      match uu___102_3442 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3443 -> false))
               in
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
                          FStar_Syntax_Print.lid_to_string lid1  in
                        let uu____3461 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3460 uu____3461
                         in
                      failwith uu____3459)
                  in
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
                     let uu____3483 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____3484 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3483 uu____3484
                      in
                   failwith uu____3482
               | uu____3490 ->
                   let uu____3493 =
                     let uu____3496 =
                       let uu____3497 = FStar_Syntax_Util.arrow binders c  in
                       (univs1, uu____3497)  in
                     inst_tscheme_with uu____3496 insts  in
                   (match uu____3493 with
                    | (uu____3505,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____3508 =
                          let uu____3509 = FStar_Syntax_Subst.compress t1  in
                          uu____3509.FStar_Syntax_Syntax.n  in
                        (match uu____3508 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3539 -> failwith "Impossible")))
        | uu____3543 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3569 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____3569 with
        | None  -> None
        | Some (uu____3576,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3581 = find1 l2  in
            (match uu____3581 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____3586 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3586 with
        | Some l1 -> l1
        | None  ->
            let uu____3589 = find1 l  in
            (match uu____3589 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____3601 = lookup_qname env l1  in
      match uu____3601 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                ne;
              FStar_Syntax_Syntax.sigrng = uu____3614;_},uu____3615),uu____3616)
          -> ne.FStar_Syntax_Syntax.qualifiers
      | uu____3640 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3663 =
          let uu____3664 =
            let uu____3665 = FStar_Util.string_of_int i  in
            let uu____3666 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3665 uu____3666
             in
          failwith uu____3664  in
        let uu____3667 = lookup_datacon env lid  in
        match uu____3667 with
        | (uu____3670,t) ->
            let uu____3672 =
              let uu____3673 = FStar_Syntax_Subst.compress t  in
              uu____3673.FStar_Syntax_Syntax.n  in
            (match uu____3672 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3677) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____3698 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right uu____3698 Prims.fst)
             | uu____3703 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3710 = lookup_qname env l  in
      match uu____3710 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3721,uu____3722,uu____3723,quals);
              FStar_Syntax_Syntax.sigrng = uu____3725;_},uu____3726),uu____3727)
          ->
          FStar_Util.for_some
            (fun uu___103_3753  ->
               match uu___103_3753 with
               | FStar_Syntax_Syntax.Projector uu____3754 -> true
               | uu____3757 -> false) quals
      | uu____3758 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3775 = lookup_qname env lid  in
      match uu____3775 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3786,uu____3787,uu____3788,uu____3789,uu____3790,uu____3791,uu____3792);
              FStar_Syntax_Syntax.sigrng = uu____3793;_},uu____3794),uu____3795)
          -> true
      | uu____3823 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3840 = lookup_qname env lid  in
      match uu____3840 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3851,uu____3852,uu____3853,uu____3854,uu____3855,uu____3856,tags);
              FStar_Syntax_Syntax.sigrng = uu____3858;_},uu____3859),uu____3860)
          ->
          FStar_Util.for_some
            (fun uu___104_3890  ->
               match uu___104_3890 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3893 -> false) tags
      | uu____3894 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3911 = lookup_qname env lid  in
      match uu____3911 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3922,uu____3923,tags,uu____3925);
              FStar_Syntax_Syntax.sigrng = uu____3926;_},uu____3927),uu____3928)
          ->
          FStar_Util.for_some
            (fun uu___105_3958  ->
               match uu___105_3958 with
               | FStar_Syntax_Syntax.Action uu____3959 -> true
               | uu____3960 -> false) tags
      | uu____3961 -> false
  
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
      let uu____3980 =
        let uu____3981 = FStar_Syntax_Util.un_uinst head1  in
        uu____3981.FStar_Syntax_Syntax.n  in
      match uu____3980 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3985 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____4023 -> Some false
        | FStar_Util.Inr (se,uu____4032) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____4041,uu____4042,uu____4043,qs) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4047 -> Some true
             | uu____4058 -> Some false)
         in
      let uu____4059 =
        let uu____4061 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____4061 mapper  in
      match uu____4059 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4088 = lookup_qname env lid  in
      match uu____4088 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4099,uu____4100,tps,uu____4102,uu____4103,uu____4104,uu____4105);
              FStar_Syntax_Syntax.sigrng = uu____4106;_},uu____4107),uu____4108)
          -> FStar_List.length tps
      | uu____4141 ->
          let uu____4152 =
            let uu____4153 =
              let uu____4156 = name_not_found lid  in
              (uu____4156, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____4153  in
          Prims.raise uu____4152
  
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
      let uu____4173 = effect_decl_opt env l  in
      match uu____4173 with
      | None  ->
          let uu____4175 =
            let uu____4176 =
              let uu____4179 = name_not_found l  in
              (uu____4179, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____4176  in
          Prims.raise uu____4175
      | Some md -> md
  
let identity_mlift : mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term = (Some (fun t  -> fun wp  -> fun e  -> e))
  } 
let join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift)
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
            (let uu____4215 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4239  ->
                       match uu____4239 with
                       | (m1,m2,uu____4247,uu____4248,uu____4249) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____4215 with
             | None  ->
                 let uu____4258 =
                   let uu____4259 =
                     let uu____4262 =
                       let uu____4263 = FStar_Syntax_Print.lid_to_string l1
                          in
                       let uu____4264 = FStar_Syntax_Print.lid_to_string l2
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4263
                         uu____4264
                        in
                     (uu____4262, (env.range))  in
                   FStar_Errors.Error uu____4259  in
                 Prims.raise uu____4258
             | Some (uu____4268,uu____4269,m3,j1,j2) -> (m3, j1, j2))
  
let monad_leq :
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
  
let wp_sig_aux :
  FStar_Syntax_Syntax.eff_decl Prims.list ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____4306 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____4306 with
      | None  ->
          let uu____4315 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____4315
      | Some md ->
          let uu____4321 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____4321 with
           | (uu____4328,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____4336)::(wp,uu____4338)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____4360 -> failwith "Impossible"))
  
let wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
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
                 let uu____4395 = get_range env  in
                 let uu____4396 =
                   let uu____4399 =
                     let uu____4400 =
                       let uu____4410 =
                         let uu____4412 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____4412]  in
                       (null_wp, uu____4410)  in
                     FStar_Syntax_Syntax.Tm_app uu____4400  in
                   FStar_Syntax_Syntax.mk uu____4399  in
                 uu____4396 None uu____4395  in
               let uu____4422 =
                 let uu____4423 =
                   let uu____4429 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____4429]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4423;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____4422)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___116_4438 = env.effects  in
            {
              decls = (ne :: ((env.effects).decls));
              order = (uu___116_4438.order);
              joins = (uu___116_4438.joins)
            }  in
          let uu___117_4439 = env  in
          {
            solver = (uu___117_4439.solver);
            range = (uu___117_4439.range);
            curmodule = (uu___117_4439.curmodule);
            gamma = (uu___117_4439.gamma);
            gamma_cache = (uu___117_4439.gamma_cache);
            modules = (uu___117_4439.modules);
            expected_typ = (uu___117_4439.expected_typ);
            sigtab = (uu___117_4439.sigtab);
            is_pattern = (uu___117_4439.is_pattern);
            instantiate_imp = (uu___117_4439.instantiate_imp);
            effects;
            generalize = (uu___117_4439.generalize);
            letrecs = (uu___117_4439.letrecs);
            top_level = (uu___117_4439.top_level);
            check_uvars = (uu___117_4439.check_uvars);
            use_eq = (uu___117_4439.use_eq);
            is_iface = (uu___117_4439.is_iface);
            admit = (uu___117_4439.admit);
            lax = (uu___117_4439.lax);
            lax_universes = (uu___117_4439.lax_universes);
            type_of = (uu___117_4439.type_of);
            universe_of = (uu___117_4439.universe_of);
            use_bv_sorts = (uu___117_4439.use_bv_sorts);
            qname_and_index = (uu___117_4439.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4456 = (e1.mlift).mlift_wp r wp1  in
                (e2.mlift).mlift_wp r uu____4456  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4535 = (e1.mlift).mlift_wp t wp  in
                              let uu____4536 = l1 t wp e  in
                              l2 t uu____4535 uu____4536))
                | uu____4537 -> None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4572 = inst_tscheme lift_t  in
            match uu____4572 with
            | (uu____4577,lift_t1) ->
                let uu____4579 =
                  let uu____4582 =
                    let uu____4583 =
                      let uu____4593 =
                        let uu____4595 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4596 =
                          let uu____4598 = FStar_Syntax_Syntax.as_arg wp1  in
                          [uu____4598]  in
                        uu____4595 :: uu____4596  in
                      (lift_t1, uu____4593)  in
                    FStar_Syntax_Syntax.Tm_app uu____4583  in
                  FStar_Syntax_Syntax.mk uu____4582  in
                uu____4579 None wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4643 = inst_tscheme lift_t  in
            match uu____4643 with
            | (uu____4648,lift_t1) ->
                let uu____4650 =
                  let uu____4653 =
                    let uu____4654 =
                      let uu____4664 =
                        let uu____4666 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4667 =
                          let uu____4669 = FStar_Syntax_Syntax.as_arg wp1  in
                          let uu____4670 =
                            let uu____4672 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____4672]  in
                          uu____4669 :: uu____4670  in
                        uu____4666 :: uu____4667  in
                      (lift_t1, uu____4664)  in
                    FStar_Syntax_Syntax.Tm_app uu____4654  in
                  FStar_Syntax_Syntax.mk uu____4653  in
                uu____4650 None e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____4713 =
                let uu____4714 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____4714
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____4713  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____4718 =
              let uu____4719 = l.mlift_wp arg wp  in
              FStar_Syntax_Print.term_to_string uu____4719  in
            let uu____4720 =
              let uu____4721 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4736 = l1 arg wp e  in
                     FStar_Syntax_Print.term_to_string uu____4736)
                 in
              FStar_Util.dflt "none" uu____4721  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4718
              uu____4720
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____4754 =
            match uu____4754 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_28  -> Some _0_28)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____4779 =
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
                                    (let uu____4791 =
                                       let uu____4796 =
                                         find_edge order1 (i, k)  in
                                       let uu____4798 =
                                         find_edge order1 (k, j)  in
                                       (uu____4796, uu____4798)  in
                                     match uu____4791 with
                                     | (Some e1,Some e2) ->
                                         let uu____4807 = compose_edges e1 e2
                                            in
                                         [uu____4807]
                                     | uu____4808 -> [])))))
                 in
              FStar_List.append order1 uu____4779  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____4823 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4824 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____4824
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____4823
                   then
                     let uu____4827 =
                       let uu____4828 =
                         let uu____4831 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         let uu____4832 = get_range env  in
                         (uu____4831, uu____4832)  in
                       FStar_Errors.Error uu____4828  in
                     Prims.raise uu____4827
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
                                            let uu____4895 =
                                              let uu____4900 =
                                                find_edge order2 (i, k)  in
                                              let uu____4902 =
                                                find_edge order2 (j, k)  in
                                              (uu____4900, uu____4902)  in
                                            match uu____4895 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____4925,uu____4926)
                                                     ->
                                                     let uu____4930 =
                                                       let uu____4933 =
                                                         let uu____4934 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____4934
                                                          in
                                                       let uu____4936 =
                                                         let uu____4937 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____4937
                                                          in
                                                       (uu____4933,
                                                         uu____4936)
                                                        in
                                                     (match uu____4930 with
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
                                            | uu____4956 -> bopt) None)
                                 in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___118_4995 = env.effects  in
              { decls = (uu___118_4995.decls); order = order2; joins }  in
            let uu___119_4996 = env  in
            {
              solver = (uu___119_4996.solver);
              range = (uu___119_4996.range);
              curmodule = (uu___119_4996.curmodule);
              gamma = (uu___119_4996.gamma);
              gamma_cache = (uu___119_4996.gamma_cache);
              modules = (uu___119_4996.modules);
              expected_typ = (uu___119_4996.expected_typ);
              sigtab = (uu___119_4996.sigtab);
              is_pattern = (uu___119_4996.is_pattern);
              instantiate_imp = (uu___119_4996.instantiate_imp);
              effects;
              generalize = (uu___119_4996.generalize);
              letrecs = (uu___119_4996.letrecs);
              top_level = (uu___119_4996.top_level);
              check_uvars = (uu___119_4996.check_uvars);
              use_eq = (uu___119_4996.use_eq);
              is_iface = (uu___119_4996.is_iface);
              admit = (uu___119_4996.admit);
              lax = (uu___119_4996.lax);
              lax_universes = (uu___119_4996.lax_universes);
              type_of = (uu___119_4996.type_of);
              universe_of = (uu___119_4996.universe_of);
              use_bv_sorts = (uu___119_4996.use_bv_sorts);
              qname_and_index = (uu___119_4996.qname_and_index)
            }))
      | uu____4997 -> env
  
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
        | uu____5019 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____5027 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____5027 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5037 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____5037 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5054 =
                     let uu____5055 =
                       let uu____5058 =
                         let uu____5059 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____5065 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1"))
                            in
                         let uu____5073 =
                           let uu____5074 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____5074  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5059 uu____5065 uu____5073
                          in
                       (uu____5058, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____5055  in
                   Prims.raise uu____5054)
                else ();
                (let inst1 =
                   let uu____5078 =
                     let uu____5084 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____5084 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____5091  ->
                        fun uu____5092  ->
                          match (uu____5091, uu____5092) with
                          | ((x,uu____5106),(t,uu____5108)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5078
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____5123 =
                     let uu___120_5124 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___120_5124.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___120_5124.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___120_5124.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___120_5124.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____5123
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux only_reifiable env c u_c =
  let uu____5154 =
    let uu____5156 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)
       in
    effect_decl_opt env uu____5156  in
  match uu____5154 with
  | None  -> None
  | Some ed ->
      let uu____5163 =
        only_reifiable &&
          (let uu____5164 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____5164)
         in
      if uu____5163
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5177 ->
             let c1 = unfold_effect_abbrev env c  in
             let uu____5179 =
               let uu____5188 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5188)  in
             (match uu____5179 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr))
                     in
                  let uu____5222 =
                    let uu____5225 = get_range env  in
                    let uu____5226 =
                      let uu____5229 =
                        let uu____5230 =
                          let uu____5240 =
                            let uu____5242 =
                              FStar_Syntax_Syntax.as_arg res_typ  in
                            [uu____5242; wp]  in
                          (repr, uu____5240)  in
                        FStar_Syntax_Syntax.Tm_app uu____5230  in
                      FStar_Syntax_Syntax.mk uu____5229  in
                    uu____5226 None uu____5225  in
                  Some uu____5222))
  
let effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax Prims.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____5286 =
            let uu____5287 =
              let uu____5290 =
                let uu____5291 = FStar_Ident.string_of_lid l  in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5291
                 in
              let uu____5292 = get_range env  in (uu____5290, uu____5292)  in
            FStar_Errors.Error uu____5287  in
          Prims.raise uu____5286  in
        let uu____5293 = effect_repr_aux true env c u_c  in
        match uu____5293 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
  
let is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let is_reifiable :
  env ->
    (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either -> Prims.bool
  =
  fun env  ->
    fun c  ->
      let effect_lid =
        match c with
        | FStar_Util.Inl lc -> lc.FStar_Syntax_Syntax.eff_name
        | FStar_Util.Inr (eff_name,uu____5325) -> eff_name  in
      is_reifiable_effect env effect_lid
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5338 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5345 =
        let uu____5346 = FStar_Syntax_Subst.compress t  in
        uu____5346.FStar_Syntax_Syntax.n  in
      match uu____5345 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5349,c) ->
          is_reifiable_comp env c
      | uu____5361 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5386 = push1 x rest1  in local :: uu____5386
         in
      let uu___121_5388 = env  in
      let uu____5389 = push1 s env.gamma  in
      {
        solver = (uu___121_5388.solver);
        range = (uu___121_5388.range);
        curmodule = (uu___121_5388.curmodule);
        gamma = uu____5389;
        gamma_cache = (uu___121_5388.gamma_cache);
        modules = (uu___121_5388.modules);
        expected_typ = (uu___121_5388.expected_typ);
        sigtab = (uu___121_5388.sigtab);
        is_pattern = (uu___121_5388.is_pattern);
        instantiate_imp = (uu___121_5388.instantiate_imp);
        effects = (uu___121_5388.effects);
        generalize = (uu___121_5388.generalize);
        letrecs = (uu___121_5388.letrecs);
        top_level = (uu___121_5388.top_level);
        check_uvars = (uu___121_5388.check_uvars);
        use_eq = (uu___121_5388.use_eq);
        is_iface = (uu___121_5388.is_iface);
        admit = (uu___121_5388.admit);
        lax = (uu___121_5388.lax);
        lax_universes = (uu___121_5388.lax_universes);
        type_of = (uu___121_5388.type_of);
        universe_of = (uu___121_5388.universe_of);
        use_bv_sorts = (uu___121_5388.use_bv_sorts);
        qname_and_index = (uu___121_5388.qname_and_index)
      }
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env1 s
  
let push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env1 s
  
let push_local_binding : env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___122_5416 = env  in
      {
        solver = (uu___122_5416.solver);
        range = (uu___122_5416.range);
        curmodule = (uu___122_5416.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___122_5416.gamma_cache);
        modules = (uu___122_5416.modules);
        expected_typ = (uu___122_5416.expected_typ);
        sigtab = (uu___122_5416.sigtab);
        is_pattern = (uu___122_5416.is_pattern);
        instantiate_imp = (uu___122_5416.instantiate_imp);
        effects = (uu___122_5416.effects);
        generalize = (uu___122_5416.generalize);
        letrecs = (uu___122_5416.letrecs);
        top_level = (uu___122_5416.top_level);
        check_uvars = (uu___122_5416.check_uvars);
        use_eq = (uu___122_5416.use_eq);
        is_iface = (uu___122_5416.is_iface);
        admit = (uu___122_5416.admit);
        lax = (uu___122_5416.lax);
        lax_universes = (uu___122_5416.lax_universes);
        type_of = (uu___122_5416.type_of);
        universe_of = (uu___122_5416.universe_of);
        use_bv_sorts = (uu___122_5416.use_bv_sorts);
        qname_and_index = (uu___122_5416.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let pop_bv : env -> (FStar_Syntax_Syntax.bv * env) Prims.option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___123_5437 = env  in
             {
               solver = (uu___123_5437.solver);
               range = (uu___123_5437.range);
               curmodule = (uu___123_5437.curmodule);
               gamma = rest;
               gamma_cache = (uu___123_5437.gamma_cache);
               modules = (uu___123_5437.modules);
               expected_typ = (uu___123_5437.expected_typ);
               sigtab = (uu___123_5437.sigtab);
               is_pattern = (uu___123_5437.is_pattern);
               instantiate_imp = (uu___123_5437.instantiate_imp);
               effects = (uu___123_5437.effects);
               generalize = (uu___123_5437.generalize);
               letrecs = (uu___123_5437.letrecs);
               top_level = (uu___123_5437.top_level);
               check_uvars = (uu___123_5437.check_uvars);
               use_eq = (uu___123_5437.use_eq);
               is_iface = (uu___123_5437.is_iface);
               admit = (uu___123_5437.admit);
               lax = (uu___123_5437.lax);
               lax_universes = (uu___123_5437.lax_universes);
               type_of = (uu___123_5437.type_of);
               universe_of = (uu___123_5437.universe_of);
               use_bv_sorts = (uu___123_5437.use_bv_sorts);
               qname_and_index = (uu___123_5437.qname_and_index)
             }))
    | uu____5438 -> None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5451  ->
             match uu____5451 with | (x,uu____5455) -> push_bv env1 x) env bs
  
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
            let uu___124_5475 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___124_5475.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___124_5475.FStar_Syntax_Syntax.index);
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
      (let uu___125_5505 = env  in
       {
         solver = (uu___125_5505.solver);
         range = (uu___125_5505.range);
         curmodule = (uu___125_5505.curmodule);
         gamma = [];
         gamma_cache = (uu___125_5505.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___125_5505.sigtab);
         is_pattern = (uu___125_5505.is_pattern);
         instantiate_imp = (uu___125_5505.instantiate_imp);
         effects = (uu___125_5505.effects);
         generalize = (uu___125_5505.generalize);
         letrecs = (uu___125_5505.letrecs);
         top_level = (uu___125_5505.top_level);
         check_uvars = (uu___125_5505.check_uvars);
         use_eq = (uu___125_5505.use_eq);
         is_iface = (uu___125_5505.is_iface);
         admit = (uu___125_5505.admit);
         lax = (uu___125_5505.lax);
         lax_universes = (uu___125_5505.lax_universes);
         type_of = (uu___125_5505.type_of);
         universe_of = (uu___125_5505.universe_of);
         use_bv_sorts = (uu___125_5505.use_bv_sorts);
         qname_and_index = (uu___125_5505.qname_and_index)
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
      let uu___126_5520 = env  in
      {
        solver = (uu___126_5520.solver);
        range = (uu___126_5520.range);
        curmodule = (uu___126_5520.curmodule);
        gamma = (uu___126_5520.gamma);
        gamma_cache = (uu___126_5520.gamma_cache);
        modules = (uu___126_5520.modules);
        expected_typ = (Some t);
        sigtab = (uu___126_5520.sigtab);
        is_pattern = (uu___126_5520.is_pattern);
        instantiate_imp = (uu___126_5520.instantiate_imp);
        effects = (uu___126_5520.effects);
        generalize = (uu___126_5520.generalize);
        letrecs = (uu___126_5520.letrecs);
        top_level = (uu___126_5520.top_level);
        check_uvars = (uu___126_5520.check_uvars);
        use_eq = false;
        is_iface = (uu___126_5520.is_iface);
        admit = (uu___126_5520.admit);
        lax = (uu___126_5520.lax);
        lax_universes = (uu___126_5520.lax_universes);
        type_of = (uu___126_5520.type_of);
        universe_of = (uu___126_5520.universe_of);
        use_bv_sorts = (uu___126_5520.use_bv_sorts);
        qname_and_index = (uu___126_5520.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let uu____5536 = expected_typ env_  in
    ((let uu___127_5539 = env_  in
      {
        solver = (uu___127_5539.solver);
        range = (uu___127_5539.range);
        curmodule = (uu___127_5539.curmodule);
        gamma = (uu___127_5539.gamma);
        gamma_cache = (uu___127_5539.gamma_cache);
        modules = (uu___127_5539.modules);
        expected_typ = None;
        sigtab = (uu___127_5539.sigtab);
        is_pattern = (uu___127_5539.is_pattern);
        instantiate_imp = (uu___127_5539.instantiate_imp);
        effects = (uu___127_5539.effects);
        generalize = (uu___127_5539.generalize);
        letrecs = (uu___127_5539.letrecs);
        top_level = (uu___127_5539.top_level);
        check_uvars = (uu___127_5539.check_uvars);
        use_eq = false;
        is_iface = (uu___127_5539.is_iface);
        admit = (uu___127_5539.admit);
        lax = (uu___127_5539.lax);
        lax_universes = (uu___127_5539.lax_universes);
        type_of = (uu___127_5539.type_of);
        universe_of = (uu___127_5539.universe_of);
        use_bv_sorts = (uu___127_5539.use_bv_sorts);
        qname_and_index = (uu___127_5539.qname_and_index)
      }), uu____5536)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5550 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___106_5554  ->
                    match uu___106_5554 with
                    | Binding_sig (uu____5556,se) -> [se]
                    | uu____5560 -> []))
             in
          FStar_All.pipe_right uu____5550 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___128_5565 = env  in
       {
         solver = (uu___128_5565.solver);
         range = (uu___128_5565.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___128_5565.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___128_5565.expected_typ);
         sigtab = (uu___128_5565.sigtab);
         is_pattern = (uu___128_5565.is_pattern);
         instantiate_imp = (uu___128_5565.instantiate_imp);
         effects = (uu___128_5565.effects);
         generalize = (uu___128_5565.generalize);
         letrecs = (uu___128_5565.letrecs);
         top_level = (uu___128_5565.top_level);
         check_uvars = (uu___128_5565.check_uvars);
         use_eq = (uu___128_5565.use_eq);
         is_iface = (uu___128_5565.is_iface);
         admit = (uu___128_5565.admit);
         lax = (uu___128_5565.lax);
         lax_universes = (uu___128_5565.lax_universes);
         type_of = (uu___128_5565.type_of);
         universe_of = (uu___128_5565.universe_of);
         use_bv_sorts = (uu___128_5565.use_bv_sorts);
         qname_and_index = (uu___128_5565.qname_and_index)
       })
  
let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5615)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5630 =
            let uu____5634 = FStar_Syntax_Free.uvars t  in ext out uu____5634
             in
          aux uu____5630 tl1
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
          let uu____5690 =
            let uu____5692 = FStar_Syntax_Free.univs t  in ext out uu____5692
             in
          aux uu____5690 tl1
      | (Binding_sig uu____5694)::uu____5695 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5732)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5742 = FStar_Util.set_add uname out  in
          aux uu____5742 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5756 =
            let uu____5758 = FStar_Syntax_Free.univnames t  in
            ext out uu____5758  in
          aux uu____5756 tl1
      | (Binding_sig uu____5760)::uu____5761 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___107_5777  ->
            match uu___107_5777 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5789 =
      let uu____5791 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____5791
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____5789 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____5807 =
      let uu____5808 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___108_5812  ->
                match uu___108_5812 with
                | Binding_var x ->
                    let uu____5814 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____5814
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____5817) ->
                    let uu____5818 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____5818
                | Binding_sig (ls,uu____5820) ->
                    let uu____5823 =
                      let uu____5824 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____5824
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____5823
                | Binding_sig_inst (ls,uu____5830,uu____5831) ->
                    let uu____5834 =
                      let uu____5835 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____5835
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____5834))
         in
      FStar_All.pipe_right uu____5808 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____5807 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____5847 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____5847
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____5864  ->
                 fun uu____5865  ->
                   match (uu____5864, uu____5865) with
                   | ((b1,uu____5875),(b2,uu____5877)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___109_5920  ->
             match uu___109_5920 with
             | Binding_sig (lids,uu____5924) -> FStar_List.append lids keys
             | uu____5927 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____5929  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let dummy_solver : solver_t =
  {
    init = (fun uu____5933  -> ());
    push = (fun uu____5934  -> ());
    pop = (fun uu____5935  -> ());
    mark = (fun uu____5936  -> ());
    reset_mark = (fun uu____5937  -> ());
    commit_mark = (fun uu____5938  -> ());
    encode_modul = (fun uu____5939  -> fun uu____5940  -> ());
    encode_sig = (fun uu____5941  -> fun uu____5942  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____5949  -> fun uu____5950  -> fun uu____5951  -> ());
    is_trivial = (fun uu____5955  -> fun uu____5956  -> false);
    finish = (fun uu____5957  -> ());
    refresh = (fun uu____5958  -> ())
  } 