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
    (let uu___108_1170 = env  in
     let uu____1171 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____1173 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___108_1170.solver);
       range = (uu___108_1170.range);
       curmodule = (uu___108_1170.curmodule);
       gamma = (uu___108_1170.gamma);
       gamma_cache = uu____1171;
       modules = (uu___108_1170.modules);
       expected_typ = (uu___108_1170.expected_typ);
       sigtab = uu____1173;
       is_pattern = (uu___108_1170.is_pattern);
       instantiate_imp = (uu___108_1170.instantiate_imp);
       effects = (uu___108_1170.effects);
       generalize = (uu___108_1170.generalize);
       letrecs = (uu___108_1170.letrecs);
       top_level = (uu___108_1170.top_level);
       check_uvars = (uu___108_1170.check_uvars);
       use_eq = (uu___108_1170.use_eq);
       is_iface = (uu___108_1170.is_iface);
       admit = (uu___108_1170.admit);
       lax = (uu___108_1170.lax);
       lax_universes = (uu___108_1170.lax_universes);
       type_of = (uu___108_1170.type_of);
       universe_of = (uu___108_1170.universe_of);
       use_bv_sorts = (uu___108_1170.use_bv_sorts);
       qname_and_index = (uu___108_1170.qname_and_index)
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
              (let uu___109_1262 = env  in
               {
                 solver = (uu___109_1262.solver);
                 range = (uu___109_1262.range);
                 curmodule = (uu___109_1262.curmodule);
                 gamma = (uu___109_1262.gamma);
                 gamma_cache = (uu___109_1262.gamma_cache);
                 modules = (uu___109_1262.modules);
                 expected_typ = (uu___109_1262.expected_typ);
                 sigtab = (uu___109_1262.sigtab);
                 is_pattern = (uu___109_1262.is_pattern);
                 instantiate_imp = (uu___109_1262.instantiate_imp);
                 effects = (uu___109_1262.effects);
                 generalize = (uu___109_1262.generalize);
                 letrecs = (uu___109_1262.letrecs);
                 top_level = (uu___109_1262.top_level);
                 check_uvars = (uu___109_1262.check_uvars);
                 use_eq = (uu___109_1262.use_eq);
                 is_iface = (uu___109_1262.is_iface);
                 admit = (uu___109_1262.admit);
                 lax = (uu___109_1262.lax);
                 lax_universes = (uu___109_1262.lax_universes);
                 type_of = (uu___109_1262.type_of);
                 universe_of = (uu___109_1262.universe_of);
                 use_bv_sorts = (uu___109_1262.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1265,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___110_1271 = env  in
               {
                 solver = (uu___110_1271.solver);
                 range = (uu___110_1271.range);
                 curmodule = (uu___110_1271.curmodule);
                 gamma = (uu___110_1271.gamma);
                 gamma_cache = (uu___110_1271.gamma_cache);
                 modules = (uu___110_1271.modules);
                 expected_typ = (uu___110_1271.expected_typ);
                 sigtab = (uu___110_1271.sigtab);
                 is_pattern = (uu___110_1271.is_pattern);
                 instantiate_imp = (uu___110_1271.instantiate_imp);
                 effects = (uu___110_1271.effects);
                 generalize = (uu___110_1271.generalize);
                 letrecs = (uu___110_1271.letrecs);
                 top_level = (uu___110_1271.top_level);
                 check_uvars = (uu___110_1271.check_uvars);
                 use_eq = (uu___110_1271.use_eq);
                 is_iface = (uu___110_1271.is_iface);
                 admit = (uu___110_1271.admit);
                 lax = (uu___110_1271.lax);
                 lax_universes = (uu___110_1271.lax_universes);
                 type_of = (uu___110_1271.type_of);
                 universe_of = (uu___110_1271.universe_of);
                 use_bv_sorts = (uu___110_1271.use_bv_sorts);
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
        (let uu___111_1287 = e  in
         {
           solver = (uu___111_1287.solver);
           range = r;
           curmodule = (uu___111_1287.curmodule);
           gamma = (uu___111_1287.gamma);
           gamma_cache = (uu___111_1287.gamma_cache);
           modules = (uu___111_1287.modules);
           expected_typ = (uu___111_1287.expected_typ);
           sigtab = (uu___111_1287.sigtab);
           is_pattern = (uu___111_1287.is_pattern);
           instantiate_imp = (uu___111_1287.instantiate_imp);
           effects = (uu___111_1287.effects);
           generalize = (uu___111_1287.generalize);
           letrecs = (uu___111_1287.letrecs);
           top_level = (uu___111_1287.top_level);
           check_uvars = (uu___111_1287.check_uvars);
           use_eq = (uu___111_1287.use_eq);
           is_iface = (uu___111_1287.is_iface);
           admit = (uu___111_1287.admit);
           lax = (uu___111_1287.lax);
           lax_universes = (uu___111_1287.lax_universes);
           type_of = (uu___111_1287.type_of);
           universe_of = (uu___111_1287.universe_of);
           use_bv_sorts = (uu___111_1287.use_bv_sorts);
           qname_and_index = (uu___111_1287.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___112_1304 = env  in
      {
        solver = (uu___112_1304.solver);
        range = (uu___112_1304.range);
        curmodule = lid;
        gamma = (uu___112_1304.gamma);
        gamma_cache = (uu___112_1304.gamma_cache);
        modules = (uu___112_1304.modules);
        expected_typ = (uu___112_1304.expected_typ);
        sigtab = (uu___112_1304.sigtab);
        is_pattern = (uu___112_1304.is_pattern);
        instantiate_imp = (uu___112_1304.instantiate_imp);
        effects = (uu___112_1304.effects);
        generalize = (uu___112_1304.generalize);
        letrecs = (uu___112_1304.letrecs);
        top_level = (uu___112_1304.top_level);
        check_uvars = (uu___112_1304.check_uvars);
        use_eq = (uu___112_1304.use_eq);
        is_iface = (uu___112_1304.is_iface);
        admit = (uu___112_1304.admit);
        lax = (uu___112_1304.lax);
        lax_universes = (uu___112_1304.lax_universes);
        type_of = (uu___112_1304.type_of);
        universe_of = (uu___112_1304.universe_of);
        use_bv_sorts = (uu___112_1304.use_bv_sorts);
        qname_and_index = (uu___112_1304.qname_and_index)
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
  fun uu___96_1374  ->
    match uu___96_1374 with
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
                (fun uu___97_1582  ->
                   match uu___97_1582 with
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
        (fun uu___98_1943  ->
           match uu___98_1943 with
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
               (let uu___113_2585 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___113_2585.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___113_2585.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___113_2585.FStar_Syntax_Syntax.vars)
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
          let uu____2767 =
            let uu____2768 =
              let uu____2771 = name_not_found l  in
              (uu____2771, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____2768  in
          Prims.raise uu____2767
      | Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___99_2792  ->
              match uu___99_2792 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2794 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2805 = lookup_qname env lid  in
      match uu____2805 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2820,uvs,t,q);
              FStar_Syntax_Syntax.sigrng = uu____2824;_},None
            ),uu____2825)
          ->
          let uu____2850 =
            let uu____2856 =
              let uu____2859 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____2859)  in
            (uu____2856, q)  in
          Some uu____2850
      | uu____2868 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2890 = lookup_qname env lid  in
      match uu____2890 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2903,uvs,t,uu____2906);
              FStar_Syntax_Syntax.sigrng = uu____2907;_},None
            ),uu____2908)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2933 ->
          let uu____2944 =
            let uu____2945 =
              let uu____2948 = name_not_found lid  in
              (uu____2948, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____2945  in
          Prims.raise uu____2944
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2959 = lookup_qname env lid  in
      match uu____2959 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____2972,uvs,t,uu____2975,uu____2976,uu____2977,uu____2978);
              FStar_Syntax_Syntax.sigrng = uu____2979;_},None
            ),uu____2980)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3007 ->
          let uu____3018 =
            let uu____3019 =
              let uu____3022 = name_not_found lid  in
              (uu____3022, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3019  in
          Prims.raise uu____3018
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3034 = lookup_qname env lid  in
      match uu____3034 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3048,uu____3049,uu____3050,uu____3051,uu____3052,dcs,uu____3054);
              FStar_Syntax_Syntax.sigrng = uu____3055;_},uu____3056),uu____3057)
          -> (true, dcs)
      | uu____3088 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3106 = lookup_qname env lid  in
      match uu____3106 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3117,uu____3118,uu____3119,l,uu____3121,uu____3122,uu____3123);
              FStar_Syntax_Syntax.sigrng = uu____3124;_},uu____3125),uu____3126)
          -> l
      | uu____3154 ->
          let uu____3165 =
            let uu____3166 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____3166  in
          failwith uu____3165
  
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
        let uu____3190 = lookup_qname env lid  in
        match uu____3190 with
        | Some (FStar_Util.Inr (se,None ),uu____3205) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3231,lbs),uu____3233,quals,uu____3235) when
                 visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____3252 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____3252
                      then
                        let uu____3257 =
                          let uu____3261 =
                            let uu____3262 =
                              FStar_Syntax_Util.unascribe
                                lb.FStar_Syntax_Syntax.lbdef
                               in
                            FStar_Syntax_Subst.set_use_range
                              (FStar_Ident.range_of_lid lid) uu____3262
                             in
                          ((lb.FStar_Syntax_Syntax.lbunivs), uu____3261)  in
                        Some uu____3257
                      else None)
             | uu____3271 -> None)
        | uu____3274 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____3295 = lookup_qname env ftv  in
      match uu____3295 with
      | Some (FStar_Util.Inr (se,None ),uu____3308) ->
          let uu____3331 = effect_signature se  in
          (match uu____3331 with
           | None  -> None
           | Some ((uu____3342,t),r) ->
               let uu____3351 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               Some uu____3351)
      | uu____3352 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____3369 = try_lookup_effect_lid env ftv  in
      match uu____3369 with
      | None  ->
          let uu____3371 =
            let uu____3372 =
              let uu____3375 = name_not_found ftv  in
              (uu____3375, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3372  in
          Prims.raise uu____3371
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
        let uu____3389 = lookup_qname env lid0  in
        match uu____3389 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,quals,uu____3408);
                FStar_Syntax_Syntax.sigrng = uu____3409;_},None
              ),uu____3410)
            ->
            let lid1 =
              let uu____3438 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____3438  in
            let uu____3439 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___100_3441  ->
                      match uu___100_3441 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3442 -> false))
               in
            if uu____3439
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
                     (let uu____3458 =
                        let uu____3459 =
                          FStar_Syntax_Print.lid_to_string lid1  in
                        let uu____3460 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          uu____3459 uu____3460
                         in
                      failwith uu____3458)
                  in
               match (binders, univs1) with
               | ([],uu____3466) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3475,uu____3476::uu____3477::uu____3478) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid1
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   let uu____3481 =
                     let uu____3482 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____3483 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3482 uu____3483
                      in
                   failwith uu____3481
               | uu____3489 ->
                   let uu____3492 =
                     let uu____3495 =
                       let uu____3496 = FStar_Syntax_Util.arrow binders c  in
                       (univs1, uu____3496)  in
                     inst_tscheme_with uu____3495 insts  in
                   (match uu____3492 with
                    | (uu____3504,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____3507 =
                          let uu____3508 = FStar_Syntax_Subst.compress t1  in
                          uu____3508.FStar_Syntax_Syntax.n  in
                        (match uu____3507 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3538 -> failwith "Impossible")))
        | uu____3542 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3568 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____3568 with
        | None  -> None
        | Some (uu____3575,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3580 = find1 l2  in
            (match uu____3580 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____3585 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3585 with
        | Some l1 -> l1
        | None  ->
            let uu____3588 = find1 l  in
            (match uu____3588 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____3600 = lookup_qname env l1  in
      match uu____3600 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                ne;
              FStar_Syntax_Syntax.sigrng = uu____3613;_},uu____3614),uu____3615)
          -> ne.FStar_Syntax_Syntax.qualifiers
      | uu____3639 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3662 =
          let uu____3663 =
            let uu____3664 = FStar_Util.string_of_int i  in
            let uu____3665 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3664 uu____3665
             in
          failwith uu____3663  in
        let uu____3666 = lookup_datacon env lid  in
        match uu____3666 with
        | (uu____3669,t) ->
            let uu____3671 =
              let uu____3672 = FStar_Syntax_Subst.compress t  in
              uu____3672.FStar_Syntax_Syntax.n  in
            (match uu____3671 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3676) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____3697 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right uu____3697 Prims.fst)
             | uu____3702 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3709 = lookup_qname env l  in
      match uu____3709 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3720,uu____3721,uu____3722,quals);
              FStar_Syntax_Syntax.sigrng = uu____3724;_},uu____3725),uu____3726)
          ->
          FStar_Util.for_some
            (fun uu___101_3752  ->
               match uu___101_3752 with
               | FStar_Syntax_Syntax.Projector uu____3753 -> true
               | uu____3756 -> false) quals
      | uu____3757 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3774 = lookup_qname env lid  in
      match uu____3774 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3785,uu____3786,uu____3787,uu____3788,uu____3789,uu____3790,uu____3791);
              FStar_Syntax_Syntax.sigrng = uu____3792;_},uu____3793),uu____3794)
          -> true
      | uu____3822 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3839 = lookup_qname env lid  in
      match uu____3839 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3850,uu____3851,uu____3852,uu____3853,uu____3854,uu____3855,tags);
              FStar_Syntax_Syntax.sigrng = uu____3857;_},uu____3858),uu____3859)
          ->
          FStar_Util.for_some
            (fun uu___102_3889  ->
               match uu___102_3889 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3892 -> false) tags
      | uu____3893 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3910 = lookup_qname env lid  in
      match uu____3910 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____3921,uu____3922,tags,uu____3924);
              FStar_Syntax_Syntax.sigrng = uu____3925;_},uu____3926),uu____3927)
          ->
          FStar_Util.for_some
            (fun uu___103_3957  ->
               match uu___103_3957 with
               | FStar_Syntax_Syntax.Action uu____3958 -> true
               | uu____3959 -> false) tags
      | uu____3960 -> false
  
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
      let uu____3979 =
        let uu____3980 = FStar_Syntax_Util.un_uinst head1  in
        uu____3980.FStar_Syntax_Syntax.n  in
      match uu____3979 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3984 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match Prims.fst x with
        | FStar_Util.Inl uu____4022 -> Some false
        | FStar_Util.Inr (se,uu____4031) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____4040,uu____4041,uu____4042,qs) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4046 -> Some true
             | uu____4057 -> Some false)
         in
      let uu____4058 =
        let uu____4060 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____4060 mapper  in
      match uu____4058 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4087 = lookup_qname env lid  in
      match uu____4087 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4098,uu____4099,tps,uu____4101,uu____4102,uu____4103,uu____4104);
              FStar_Syntax_Syntax.sigrng = uu____4105;_},uu____4106),uu____4107)
          -> FStar_List.length tps
      | uu____4140 ->
          let uu____4151 =
            let uu____4152 =
              let uu____4155 = name_not_found lid  in
              (uu____4155, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____4152  in
          Prims.raise uu____4151
  
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
      let uu____4172 = effect_decl_opt env l  in
      match uu____4172 with
      | None  ->
          let uu____4174 =
            let uu____4175 =
              let uu____4178 = name_not_found l  in
              (uu____4178, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____4175  in
          Prims.raise uu____4174
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
            (let uu____4214 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4238  ->
                       match uu____4238 with
                       | (m1,m2,uu____4246,uu____4247,uu____4248) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____4214 with
             | None  ->
                 let uu____4257 =
                   let uu____4258 =
                     let uu____4261 =
                       let uu____4262 = FStar_Syntax_Print.lid_to_string l1
                          in
                       let uu____4263 = FStar_Syntax_Print.lid_to_string l2
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4262
                         uu____4263
                        in
                     (uu____4261, (env.range))  in
                   FStar_Errors.Error uu____4258  in
                 Prims.raise uu____4257
             | Some (uu____4267,uu____4268,m3,j1,j2) -> (m3, j1, j2))
  
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
      let uu____4305 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____4305 with
      | None  ->
          let uu____4314 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____4314
      | Some md ->
          let uu____4320 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____4320 with
           | (uu____4327,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____4335)::(wp,uu____4337)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____4359 -> failwith "Impossible"))
  
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
                 let uu____4394 = get_range env  in
                 let uu____4395 =
                   let uu____4398 =
                     let uu____4399 =
                       let uu____4409 =
                         let uu____4411 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____4411]  in
                       (null_wp, uu____4409)  in
                     FStar_Syntax_Syntax.Tm_app uu____4399  in
                   FStar_Syntax_Syntax.mk uu____4398  in
                 uu____4395 None uu____4394  in
               let uu____4421 =
                 let uu____4422 =
                   let uu____4428 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____4428]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4422;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____4421)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___114_4437 = env.effects  in
            {
              decls = (ne :: ((env.effects).decls));
              order = (uu___114_4437.order);
              joins = (uu___114_4437.joins)
            }  in
          let uu___115_4438 = env  in
          {
            solver = (uu___115_4438.solver);
            range = (uu___115_4438.range);
            curmodule = (uu___115_4438.curmodule);
            gamma = (uu___115_4438.gamma);
            gamma_cache = (uu___115_4438.gamma_cache);
            modules = (uu___115_4438.modules);
            expected_typ = (uu___115_4438.expected_typ);
            sigtab = (uu___115_4438.sigtab);
            is_pattern = (uu___115_4438.is_pattern);
            instantiate_imp = (uu___115_4438.instantiate_imp);
            effects;
            generalize = (uu___115_4438.generalize);
            letrecs = (uu___115_4438.letrecs);
            top_level = (uu___115_4438.top_level);
            check_uvars = (uu___115_4438.check_uvars);
            use_eq = (uu___115_4438.use_eq);
            is_iface = (uu___115_4438.is_iface);
            admit = (uu___115_4438.admit);
            lax = (uu___115_4438.lax);
            lax_universes = (uu___115_4438.lax_universes);
            type_of = (uu___115_4438.type_of);
            universe_of = (uu___115_4438.universe_of);
            use_bv_sorts = (uu___115_4438.use_bv_sorts);
            qname_and_index = (uu___115_4438.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4455 = (e1.mlift).mlift_wp r wp1  in
                (e2.mlift).mlift_wp r uu____4455  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4534 = (e1.mlift).mlift_wp t wp  in
                              let uu____4535 = l1 t wp e  in
                              l2 t uu____4534 uu____4535))
                | uu____4536 -> None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4571 = inst_tscheme lift_t  in
            match uu____4571 with
            | (uu____4576,lift_t1) ->
                let uu____4578 =
                  let uu____4581 =
                    let uu____4582 =
                      let uu____4592 =
                        let uu____4594 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4595 =
                          let uu____4597 = FStar_Syntax_Syntax.as_arg wp1  in
                          [uu____4597]  in
                        uu____4594 :: uu____4595  in
                      (lift_t1, uu____4592)  in
                    FStar_Syntax_Syntax.Tm_app uu____4582  in
                  FStar_Syntax_Syntax.mk uu____4581  in
                uu____4578 None wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4642 = inst_tscheme lift_t  in
            match uu____4642 with
            | (uu____4647,lift_t1) ->
                let uu____4649 =
                  let uu____4652 =
                    let uu____4653 =
                      let uu____4663 =
                        let uu____4665 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4666 =
                          let uu____4668 = FStar_Syntax_Syntax.as_arg wp1  in
                          let uu____4669 =
                            let uu____4671 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____4671]  in
                          uu____4668 :: uu____4669  in
                        uu____4665 :: uu____4666  in
                      (lift_t1, uu____4663)  in
                    FStar_Syntax_Syntax.Tm_app uu____4653  in
                  FStar_Syntax_Syntax.mk uu____4652  in
                uu____4649 None e.FStar_Syntax_Syntax.pos
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
              let uu____4712 =
                let uu____4713 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____4713
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____4712  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____4717 =
              let uu____4718 = l.mlift_wp arg wp  in
              FStar_Syntax_Print.term_to_string uu____4718  in
            let uu____4719 =
              let uu____4720 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4735 = l1 arg wp e  in
                     FStar_Syntax_Print.term_to_string uu____4735)
                 in
              FStar_Util.dflt "none" uu____4720  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4717
              uu____4719
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____4753 =
            match uu____4753 with
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
              let uu____4778 =
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
                                    (let uu____4790 =
                                       let uu____4795 =
                                         find_edge order1 (i, k)  in
                                       let uu____4797 =
                                         find_edge order1 (k, j)  in
                                       (uu____4795, uu____4797)  in
                                     match uu____4790 with
                                     | (Some e1,Some e2) ->
                                         let uu____4806 = compose_edges e1 e2
                                            in
                                         [uu____4806]
                                     | uu____4807 -> [])))))
                 in
              FStar_List.append order1 uu____4778  in
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
                   let uu____4822 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____4823 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____4823
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____4822
                   then
                     let uu____4826 =
                       let uu____4827 =
                         let uu____4830 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         let uu____4831 = get_range env  in
                         (uu____4830, uu____4831)  in
                       FStar_Errors.Error uu____4827  in
                     Prims.raise uu____4826
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
                                            let uu____4894 =
                                              let uu____4899 =
                                                find_edge order2 (i, k)  in
                                              let uu____4901 =
                                                find_edge order2 (j, k)  in
                                              (uu____4899, uu____4901)  in
                                            match uu____4894 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____4924,uu____4925)
                                                     ->
                                                     let uu____4929 =
                                                       let uu____4932 =
                                                         let uu____4933 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____4933
                                                          in
                                                       let uu____4935 =
                                                         let uu____4936 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____4936
                                                          in
                                                       (uu____4932,
                                                         uu____4935)
                                                        in
                                                     (match uu____4929 with
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
                                            | uu____4955 -> bopt) None)
                                 in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___116_4994 = env.effects  in
              { decls = (uu___116_4994.decls); order = order2; joins }  in
            let uu___117_4995 = env  in
            {
              solver = (uu___117_4995.solver);
              range = (uu___117_4995.range);
              curmodule = (uu___117_4995.curmodule);
              gamma = (uu___117_4995.gamma);
              gamma_cache = (uu___117_4995.gamma_cache);
              modules = (uu___117_4995.modules);
              expected_typ = (uu___117_4995.expected_typ);
              sigtab = (uu___117_4995.sigtab);
              is_pattern = (uu___117_4995.is_pattern);
              instantiate_imp = (uu___117_4995.instantiate_imp);
              effects;
              generalize = (uu___117_4995.generalize);
              letrecs = (uu___117_4995.letrecs);
              top_level = (uu___117_4995.top_level);
              check_uvars = (uu___117_4995.check_uvars);
              use_eq = (uu___117_4995.use_eq);
              is_iface = (uu___117_4995.is_iface);
              admit = (uu___117_4995.admit);
              lax = (uu___117_4995.lax);
              lax_universes = (uu___117_4995.lax_universes);
              type_of = (uu___117_4995.type_of);
              universe_of = (uu___117_4995.universe_of);
              use_bv_sorts = (uu___117_4995.use_bv_sorts);
              qname_and_index = (uu___117_4995.qname_and_index)
            }))
      | uu____4996 -> env
  
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
        | uu____5018 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____5026 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____5026 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5036 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____5036 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5053 =
                     let uu____5054 =
                       let uu____5057 =
                         let uu____5058 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____5064 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1"))
                            in
                         let uu____5072 =
                           let uu____5073 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____5073  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5058 uu____5064 uu____5072
                          in
                       (uu____5057, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____5054  in
                   Prims.raise uu____5053)
                else ();
                (let inst1 =
                   let uu____5077 =
                     let uu____5083 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____5083 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____5090  ->
                        fun uu____5091  ->
                          match (uu____5090, uu____5091) with
                          | ((x,uu____5105),(t,uu____5107)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5077
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____5122 =
                     let uu___118_5123 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___118_5123.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___118_5123.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___118_5123.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___118_5123.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____5122
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux only_reifiable env c u_c =
  let uu____5153 =
    let uu____5155 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)
       in
    effect_decl_opt env uu____5155  in
  match uu____5153 with
  | None  -> None
  | Some ed ->
      let uu____5162 =
        only_reifiable &&
          (let uu____5163 =
             FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____5163)
         in
      if uu____5162
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5176 ->
             let c1 = unfold_effect_abbrev env c  in
             let uu____5178 =
               let uu____5187 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5187)  in
             (match uu____5178 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr))
                     in
                  let uu____5221 =
                    let uu____5224 = get_range env  in
                    let uu____5225 =
                      let uu____5228 =
                        let uu____5229 =
                          let uu____5239 =
                            let uu____5241 =
                              FStar_Syntax_Syntax.as_arg res_typ  in
                            [uu____5241; wp]  in
                          (repr, uu____5239)  in
                        FStar_Syntax_Syntax.Tm_app uu____5229  in
                      FStar_Syntax_Syntax.mk uu____5228  in
                    uu____5225 None uu____5224  in
                  Some uu____5221))
  
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
          let uu____5285 =
            let uu____5286 =
              let uu____5289 =
                let uu____5290 = FStar_Ident.string_of_lid l  in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5290
                 in
              let uu____5291 = get_range env  in (uu____5289, uu____5291)  in
            FStar_Errors.Error uu____5286  in
          Prims.raise uu____5285  in
        let uu____5292 = effect_repr_aux true env c u_c  in
        match uu____5292 with
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
        | FStar_Util.Inr (eff_name,uu____5324) -> eff_name  in
      is_reifiable_effect env effect_lid
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5337 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5344 =
        let uu____5345 = FStar_Syntax_Subst.compress t  in
        uu____5345.FStar_Syntax_Syntax.n  in
      match uu____5344 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5348,c) ->
          is_reifiable_comp env c
      | uu____5360 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5385 = push1 x rest1  in local :: uu____5385
         in
      let uu___119_5387 = env  in
      let uu____5388 = push1 s env.gamma  in
      {
        solver = (uu___119_5387.solver);
        range = (uu___119_5387.range);
        curmodule = (uu___119_5387.curmodule);
        gamma = uu____5388;
        gamma_cache = (uu___119_5387.gamma_cache);
        modules = (uu___119_5387.modules);
        expected_typ = (uu___119_5387.expected_typ);
        sigtab = (uu___119_5387.sigtab);
        is_pattern = (uu___119_5387.is_pattern);
        instantiate_imp = (uu___119_5387.instantiate_imp);
        effects = (uu___119_5387.effects);
        generalize = (uu___119_5387.generalize);
        letrecs = (uu___119_5387.letrecs);
        top_level = (uu___119_5387.top_level);
        check_uvars = (uu___119_5387.check_uvars);
        use_eq = (uu___119_5387.use_eq);
        is_iface = (uu___119_5387.is_iface);
        admit = (uu___119_5387.admit);
        lax = (uu___119_5387.lax);
        lax_universes = (uu___119_5387.lax_universes);
        type_of = (uu___119_5387.type_of);
        universe_of = (uu___119_5387.universe_of);
        use_bv_sorts = (uu___119_5387.use_bv_sorts);
        qname_and_index = (uu___119_5387.qname_and_index)
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
      let uu___120_5415 = env  in
      {
        solver = (uu___120_5415.solver);
        range = (uu___120_5415.range);
        curmodule = (uu___120_5415.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___120_5415.gamma_cache);
        modules = (uu___120_5415.modules);
        expected_typ = (uu___120_5415.expected_typ);
        sigtab = (uu___120_5415.sigtab);
        is_pattern = (uu___120_5415.is_pattern);
        instantiate_imp = (uu___120_5415.instantiate_imp);
        effects = (uu___120_5415.effects);
        generalize = (uu___120_5415.generalize);
        letrecs = (uu___120_5415.letrecs);
        top_level = (uu___120_5415.top_level);
        check_uvars = (uu___120_5415.check_uvars);
        use_eq = (uu___120_5415.use_eq);
        is_iface = (uu___120_5415.is_iface);
        admit = (uu___120_5415.admit);
        lax = (uu___120_5415.lax);
        lax_universes = (uu___120_5415.lax_universes);
        type_of = (uu___120_5415.type_of);
        universe_of = (uu___120_5415.universe_of);
        use_bv_sorts = (uu___120_5415.use_bv_sorts);
        qname_and_index = (uu___120_5415.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let pop_bv : env -> (FStar_Syntax_Syntax.bv * env) Prims.option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___121_5436 = env  in
             {
               solver = (uu___121_5436.solver);
               range = (uu___121_5436.range);
               curmodule = (uu___121_5436.curmodule);
               gamma = rest;
               gamma_cache = (uu___121_5436.gamma_cache);
               modules = (uu___121_5436.modules);
               expected_typ = (uu___121_5436.expected_typ);
               sigtab = (uu___121_5436.sigtab);
               is_pattern = (uu___121_5436.is_pattern);
               instantiate_imp = (uu___121_5436.instantiate_imp);
               effects = (uu___121_5436.effects);
               generalize = (uu___121_5436.generalize);
               letrecs = (uu___121_5436.letrecs);
               top_level = (uu___121_5436.top_level);
               check_uvars = (uu___121_5436.check_uvars);
               use_eq = (uu___121_5436.use_eq);
               is_iface = (uu___121_5436.is_iface);
               admit = (uu___121_5436.admit);
               lax = (uu___121_5436.lax);
               lax_universes = (uu___121_5436.lax_universes);
               type_of = (uu___121_5436.type_of);
               universe_of = (uu___121_5436.universe_of);
               use_bv_sorts = (uu___121_5436.use_bv_sorts);
               qname_and_index = (uu___121_5436.qname_and_index)
             }))
    | uu____5437 -> None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5450  ->
             match uu____5450 with | (x,uu____5454) -> push_bv env1 x) env bs
  
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
            let uu___122_5474 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___122_5474.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___122_5474.FStar_Syntax_Syntax.index);
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
      (let uu___123_5504 = env  in
       {
         solver = (uu___123_5504.solver);
         range = (uu___123_5504.range);
         curmodule = (uu___123_5504.curmodule);
         gamma = [];
         gamma_cache = (uu___123_5504.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___123_5504.sigtab);
         is_pattern = (uu___123_5504.is_pattern);
         instantiate_imp = (uu___123_5504.instantiate_imp);
         effects = (uu___123_5504.effects);
         generalize = (uu___123_5504.generalize);
         letrecs = (uu___123_5504.letrecs);
         top_level = (uu___123_5504.top_level);
         check_uvars = (uu___123_5504.check_uvars);
         use_eq = (uu___123_5504.use_eq);
         is_iface = (uu___123_5504.is_iface);
         admit = (uu___123_5504.admit);
         lax = (uu___123_5504.lax);
         lax_universes = (uu___123_5504.lax_universes);
         type_of = (uu___123_5504.type_of);
         universe_of = (uu___123_5504.universe_of);
         use_bv_sorts = (uu___123_5504.use_bv_sorts);
         qname_and_index = (uu___123_5504.qname_and_index)
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
      let uu___124_5519 = env  in
      {
        solver = (uu___124_5519.solver);
        range = (uu___124_5519.range);
        curmodule = (uu___124_5519.curmodule);
        gamma = (uu___124_5519.gamma);
        gamma_cache = (uu___124_5519.gamma_cache);
        modules = (uu___124_5519.modules);
        expected_typ = (Some t);
        sigtab = (uu___124_5519.sigtab);
        is_pattern = (uu___124_5519.is_pattern);
        instantiate_imp = (uu___124_5519.instantiate_imp);
        effects = (uu___124_5519.effects);
        generalize = (uu___124_5519.generalize);
        letrecs = (uu___124_5519.letrecs);
        top_level = (uu___124_5519.top_level);
        check_uvars = (uu___124_5519.check_uvars);
        use_eq = false;
        is_iface = (uu___124_5519.is_iface);
        admit = (uu___124_5519.admit);
        lax = (uu___124_5519.lax);
        lax_universes = (uu___124_5519.lax_universes);
        type_of = (uu___124_5519.type_of);
        universe_of = (uu___124_5519.universe_of);
        use_bv_sorts = (uu___124_5519.use_bv_sorts);
        qname_and_index = (uu___124_5519.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let uu____5535 = expected_typ env_  in
    ((let uu___125_5538 = env_  in
      {
        solver = (uu___125_5538.solver);
        range = (uu___125_5538.range);
        curmodule = (uu___125_5538.curmodule);
        gamma = (uu___125_5538.gamma);
        gamma_cache = (uu___125_5538.gamma_cache);
        modules = (uu___125_5538.modules);
        expected_typ = None;
        sigtab = (uu___125_5538.sigtab);
        is_pattern = (uu___125_5538.is_pattern);
        instantiate_imp = (uu___125_5538.instantiate_imp);
        effects = (uu___125_5538.effects);
        generalize = (uu___125_5538.generalize);
        letrecs = (uu___125_5538.letrecs);
        top_level = (uu___125_5538.top_level);
        check_uvars = (uu___125_5538.check_uvars);
        use_eq = false;
        is_iface = (uu___125_5538.is_iface);
        admit = (uu___125_5538.admit);
        lax = (uu___125_5538.lax);
        lax_universes = (uu___125_5538.lax_universes);
        type_of = (uu___125_5538.type_of);
        universe_of = (uu___125_5538.universe_of);
        use_bv_sorts = (uu___125_5538.use_bv_sorts);
        qname_and_index = (uu___125_5538.qname_and_index)
      }), uu____5535)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5549 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___104_5553  ->
                    match uu___104_5553 with
                    | Binding_sig (uu____5555,se) -> [se]
                    | uu____5559 -> []))
             in
          FStar_All.pipe_right uu____5549 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___126_5564 = env  in
       {
         solver = (uu___126_5564.solver);
         range = (uu___126_5564.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___126_5564.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___126_5564.expected_typ);
         sigtab = (uu___126_5564.sigtab);
         is_pattern = (uu___126_5564.is_pattern);
         instantiate_imp = (uu___126_5564.instantiate_imp);
         effects = (uu___126_5564.effects);
         generalize = (uu___126_5564.generalize);
         letrecs = (uu___126_5564.letrecs);
         top_level = (uu___126_5564.top_level);
         check_uvars = (uu___126_5564.check_uvars);
         use_eq = (uu___126_5564.use_eq);
         is_iface = (uu___126_5564.is_iface);
         admit = (uu___126_5564.admit);
         lax = (uu___126_5564.lax);
         lax_universes = (uu___126_5564.lax_universes);
         type_of = (uu___126_5564.type_of);
         universe_of = (uu___126_5564.universe_of);
         use_bv_sorts = (uu___126_5564.use_bv_sorts);
         qname_and_index = (uu___126_5564.qname_and_index)
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
      | (Binding_univ uu____5614)::tl1 -> aux out tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5629 =
            let uu____5633 = FStar_Syntax_Free.uvars t  in ext out uu____5633
             in
          aux uu____5629 tl1
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
          let uu____5689 =
            let uu____5691 = FStar_Syntax_Free.univs t  in ext out uu____5691
             in
          aux uu____5689 tl1
      | (Binding_sig uu____5693)::uu____5694 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5731)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5741 = FStar_Util.set_add uname out  in
          aux uu____5741 tl1
      | (Binding_lid (_,(_,t)))::tl1|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl1 ->
          let uu____5755 =
            let uu____5757 = FStar_Syntax_Free.univnames t  in
            ext out uu____5757  in
          aux uu____5755 tl1
      | (Binding_sig uu____5759)::uu____5760 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___105_5776  ->
            match uu___105_5776 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____5788 =
      let uu____5790 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____5790
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____5788 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____5806 =
      let uu____5807 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___106_5811  ->
                match uu___106_5811 with
                | Binding_var x ->
                    let uu____5813 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____5813
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____5816) ->
                    let uu____5817 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____5817
                | Binding_sig (ls,uu____5819) ->
                    let uu____5822 =
                      let uu____5823 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____5823
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____5822
                | Binding_sig_inst (ls,uu____5829,uu____5830) ->
                    let uu____5833 =
                      let uu____5834 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____5834
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____5833))
         in
      FStar_All.pipe_right uu____5807 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____5806 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____5846 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____5846
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____5863  ->
                 fun uu____5864  ->
                   match (uu____5863, uu____5864) with
                   | ((b1,uu____5874),(b2,uu____5876)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___107_5919  ->
             match uu___107_5919 with
             | Binding_sig (lids,uu____5923) -> FStar_List.append lids keys
             | uu____5926 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____5928  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let dummy_solver : solver_t =
  {
    init = (fun uu____5932  -> ());
    push = (fun uu____5933  -> ());
    pop = (fun uu____5934  -> ());
    mark = (fun uu____5935  -> ());
    reset_mark = (fun uu____5936  -> ());
    commit_mark = (fun uu____5937  -> ());
    encode_modul = (fun uu____5938  -> fun uu____5939  -> ());
    encode_sig = (fun uu____5940  -> fun uu____5941  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____5948  -> fun uu____5949  -> fun uu____5950  -> ());
    is_trivial = (fun uu____5954  -> fun uu____5955  -> false);
    finish = (fun uu____5956  -> ());
    refresh = (fun uu____5957  -> ())
  } 