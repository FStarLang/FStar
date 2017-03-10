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
      | uu____807 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____817 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____825 =
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
          let _0_178 = new_gamma_cache ()  in
          let _0_177 = new_sigtab ()  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = _0_178;
            modules = [];
            expected_typ = None;
            sigtab = _0_177;
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
  fun uu____902  ->
    let uu____903 = FStar_ST.read query_indices  in
    match uu____903 with
    | [] -> failwith "Empty query indices!"
    | uu____917 ->
        let _0_181 =
          let _0_180 = FStar_List.hd (FStar_ST.read query_indices)  in
          let _0_179 = FStar_ST.read query_indices  in _0_180 :: _0_179  in
        FStar_ST.write query_indices _0_181
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____948  ->
    let uu____949 = FStar_ST.read query_indices  in
    match uu____949 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.write query_indices tl
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____985  ->
    match uu____985 with
    | (l,n) ->
        let uu____990 = FStar_ST.read query_indices  in
        (match uu____990 with
         | hd::tl -> FStar_ST.write query_indices (((l, n) :: hd) :: tl)
         | uu____1024 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1034  -> FStar_List.hd (FStar_ST.read query_indices) 
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1046  ->
    let uu____1047 = FStar_ST.read query_indices  in
    match uu____1047 with
    | hd::uu____1059::tl -> FStar_ST.write query_indices (hd :: tl)
    | uu____1086 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let _0_183 = let _0_182 = FStar_ST.read stack  in env :: _0_182  in
     FStar_ST.write stack _0_183);
    (let uu___106_1106 = env  in
     let _0_185 = FStar_Util.smap_copy (gamma_cache env)  in
     let _0_184 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___106_1106.solver);
       range = (uu___106_1106.range);
       curmodule = (uu___106_1106.curmodule);
       gamma = (uu___106_1106.gamma);
       gamma_cache = _0_185;
       modules = (uu___106_1106.modules);
       expected_typ = (uu___106_1106.expected_typ);
       sigtab = _0_184;
       is_pattern = (uu___106_1106.is_pattern);
       instantiate_imp = (uu___106_1106.instantiate_imp);
       effects = (uu___106_1106.effects);
       generalize = (uu___106_1106.generalize);
       letrecs = (uu___106_1106.letrecs);
       top_level = (uu___106_1106.top_level);
       check_uvars = (uu___106_1106.check_uvars);
       use_eq = (uu___106_1106.use_eq);
       is_iface = (uu___106_1106.is_iface);
       admit = (uu___106_1106.admit);
       lax = (uu___106_1106.lax);
       lax_universes = (uu___106_1106.lax_universes);
       type_of = (uu___106_1106.type_of);
       universe_of = (uu___106_1106.universe_of);
       use_bv_sorts = (uu___106_1106.use_bv_sorts);
       qname_and_index = (uu___106_1106.qname_and_index)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1109  ->
    let uu____1110 = FStar_ST.read stack  in
    match uu____1110 with
    | env::tl -> (FStar_ST.write stack tl; env)
    | uu____1122 -> failwith "Impossible: Too many pops"
  
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
        let uu____1172 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1184  ->
                  match uu____1184 with
                  | (m,uu____1188) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1172 with
         | None  ->
             let next = n + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___107_1193 = env  in
               {
                 solver = (uu___107_1193.solver);
                 range = (uu___107_1193.range);
                 curmodule = (uu___107_1193.curmodule);
                 gamma = (uu___107_1193.gamma);
                 gamma_cache = (uu___107_1193.gamma_cache);
                 modules = (uu___107_1193.modules);
                 expected_typ = (uu___107_1193.expected_typ);
                 sigtab = (uu___107_1193.sigtab);
                 is_pattern = (uu___107_1193.is_pattern);
                 instantiate_imp = (uu___107_1193.instantiate_imp);
                 effects = (uu___107_1193.effects);
                 generalize = (uu___107_1193.generalize);
                 letrecs = (uu___107_1193.letrecs);
                 top_level = (uu___107_1193.top_level);
                 check_uvars = (uu___107_1193.check_uvars);
                 use_eq = (uu___107_1193.use_eq);
                 is_iface = (uu___107_1193.is_iface);
                 admit = (uu___107_1193.admit);
                 lax = (uu___107_1193.lax);
                 lax_universes = (uu___107_1193.lax_universes);
                 type_of = (uu___107_1193.type_of);
                 universe_of = (uu___107_1193.universe_of);
                 use_bv_sorts = (uu___107_1193.use_bv_sorts);
                 qname_and_index = (Some (l, next))
               }))
         | Some (uu____1196,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___108_1202 = env  in
               {
                 solver = (uu___108_1202.solver);
                 range = (uu___108_1202.range);
                 curmodule = (uu___108_1202.curmodule);
                 gamma = (uu___108_1202.gamma);
                 gamma_cache = (uu___108_1202.gamma_cache);
                 modules = (uu___108_1202.modules);
                 expected_typ = (uu___108_1202.expected_typ);
                 sigtab = (uu___108_1202.sigtab);
                 is_pattern = (uu___108_1202.is_pattern);
                 instantiate_imp = (uu___108_1202.instantiate_imp);
                 effects = (uu___108_1202.effects);
                 generalize = (uu___108_1202.generalize);
                 letrecs = (uu___108_1202.letrecs);
                 top_level = (uu___108_1202.top_level);
                 check_uvars = (uu___108_1202.check_uvars);
                 use_eq = (uu___108_1202.use_eq);
                 is_iface = (uu___108_1202.is_iface);
                 admit = (uu___108_1202.admit);
                 lax = (uu___108_1202.lax);
                 lax_universes = (uu___108_1202.lax_universes);
                 type_of = (uu___108_1202.type_of);
                 universe_of = (uu___108_1202.universe_of);
                 use_bv_sorts = (uu___108_1202.use_bv_sorts);
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
        (let uu___109_1218 = e  in
         {
           solver = (uu___109_1218.solver);
           range = r;
           curmodule = (uu___109_1218.curmodule);
           gamma = (uu___109_1218.gamma);
           gamma_cache = (uu___109_1218.gamma_cache);
           modules = (uu___109_1218.modules);
           expected_typ = (uu___109_1218.expected_typ);
           sigtab = (uu___109_1218.sigtab);
           is_pattern = (uu___109_1218.is_pattern);
           instantiate_imp = (uu___109_1218.instantiate_imp);
           effects = (uu___109_1218.effects);
           generalize = (uu___109_1218.generalize);
           letrecs = (uu___109_1218.letrecs);
           top_level = (uu___109_1218.top_level);
           check_uvars = (uu___109_1218.check_uvars);
           use_eq = (uu___109_1218.use_eq);
           is_iface = (uu___109_1218.is_iface);
           admit = (uu___109_1218.admit);
           lax = (uu___109_1218.lax);
           lax_universes = (uu___109_1218.lax_universes);
           type_of = (uu___109_1218.type_of);
           universe_of = (uu___109_1218.universe_of);
           use_bv_sorts = (uu___109_1218.use_bv_sorts);
           qname_and_index = (uu___109_1218.qname_and_index)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___110_1235 = env  in
      {
        solver = (uu___110_1235.solver);
        range = (uu___110_1235.range);
        curmodule = lid;
        gamma = (uu___110_1235.gamma);
        gamma_cache = (uu___110_1235.gamma_cache);
        modules = (uu___110_1235.modules);
        expected_typ = (uu___110_1235.expected_typ);
        sigtab = (uu___110_1235.sigtab);
        is_pattern = (uu___110_1235.is_pattern);
        instantiate_imp = (uu___110_1235.instantiate_imp);
        effects = (uu___110_1235.effects);
        generalize = (uu___110_1235.generalize);
        letrecs = (uu___110_1235.letrecs);
        top_level = (uu___110_1235.top_level);
        check_uvars = (uu___110_1235.check_uvars);
        use_eq = (uu___110_1235.use_eq);
        is_iface = (uu___110_1235.is_iface);
        admit = (uu___110_1235.admit);
        lax = (uu___110_1235.lax);
        lax_universes = (uu___110_1235.lax_universes);
        type_of = (uu___110_1235.type_of);
        universe_of = (uu___110_1235.universe_of);
        use_bv_sorts = (uu___110_1235.use_bv_sorts);
        qname_and_index = (uu___110_1235.qname_and_index)
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
  fun v  ->
    let _0_186 = FStar_Syntax_Print.bv_to_string v  in
    FStar_Util.format1 "Variable \"%s\" not found" _0_186
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1259  -> FStar_Syntax_Syntax.U_unif (FStar_Unionfind.fresh None) 
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1280) ->
          let n = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n - i), u)))
             in
          let _0_187 = FStar_Syntax_Subst.subst vs t  in (us, _0_187)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun uu___93_1300  ->
    match uu___93_1300 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1314  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1324 = inst_tscheme t  in
      match uu____1324 with
      | (us,t) ->
          let _0_188 = FStar_Syntax_Subst.set_use_range r t  in (us, _0_188)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1342  ->
          match uu____1342 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if (FStar_List.length insts) <> (FStar_List.length univs)
                    then
                      failwith
                        (let _0_192 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs)
                            in
                         let _0_191 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let _0_190 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let _0_189 = FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           _0_192 _0_191 _0_190 _0_189)
                    else ();
                    Prims.snd
                      (inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts))
               | uu____1362 ->
                   failwith
                     (let _0_193 =
                        FStar_Syntax_Print.lid_to_string
                          ed.FStar_Syntax_Syntax.mname
                         in
                      FStar_Util.format1
                        "Unexpected use of an uninstantiated effect: %s\n"
                        _0_193))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1366 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1370 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1374 -> false
  
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
             | ([],uu____1400) -> Maybe
             | (uu____1404,[]) -> No
             | (hd::tl,hd'::tl') when
                 hd.FStar_Ident.idText = hd'.FStar_Ident.idText -> aux tl tl'
             | uu____1416 -> No  in
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
          let uu____1468 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1468 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___94_1485  ->
                   match uu___94_1485 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then Some (FStar_Util.Inl (inst_tscheme t))
                       else None
                   | Binding_sig
                       (uu____1524,FStar_Syntax_Syntax.Sig_bundle
                        (ses,uu____1526,uu____1527,uu____1528))
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1538 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1538
                            then cache (FStar_Util.Inr (se, None))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1558 ->
                             Some t
                         | uu____1565 -> cache t  in
                       let uu____1566 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1566
                       then maybe_cache (FStar_Util.Inr (s, None))
                       else None
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1595 =
                         FStar_All.pipe_right lids
                           (FStar_Util.for_some (FStar_Ident.lid_equals lid))
                          in
                       if uu____1595
                       then Some (FStar_Util.Inr (s, (Some us)))
                       else None
                   | uu____1626 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1660 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____1660
         then
           let uu____1669 = find_in_sigtab env lid  in
           match uu____1669 with
           | Some se -> Some (FStar_Util.Inr (se, None))
           | None  -> None
         else None)
  
let rec add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1720,uu____1721,uu____1722)
          -> add_sigelts env ses
      | uu____1729 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se with
            | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1735) ->
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
            | uu____1739 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___95_1755  ->
           match uu___95_1755 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some (id.FStar_Syntax_Syntax.sort)
           | uu____1762 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    fun lid  ->
      match se with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1777,lb::[]),uu____1779,uu____1780,uu____1781,uu____1782)
          ->
          Some
            (inst_tscheme
               ((lb.FStar_Syntax_Syntax.lbunivs),
                 (lb.FStar_Syntax_Syntax.lbtyp)))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____1798,lbs),uu____1800,uu____1801,uu____1802,uu____1803) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____1821 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____1826 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____1826
                   then
                     Some
                       (inst_tscheme
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbtyp)))
                   else None)
      | uu____1838 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option
  =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____1851) ->
        Some
          (inst_tscheme
             (let _0_195 =
                let _0_194 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _0_194
                 in
              ((ne.FStar_Syntax_Syntax.univs), _0_195)))
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____1859,uu____1860,uu____1861,uu____1862) ->
        Some
          (inst_tscheme
             (let _0_197 =
                let _0_196 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders _0_196  in
              (us, _0_197)))
    | uu____1871 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu___96_1898 =
        match uu___96_1898 with
        | FStar_Util.Inl t -> Some t
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_datacon
             (uu____1919,uvs,t,uu____1922,uu____1923,uu____1924,uu____1925,uu____1926),None
             )
            -> Some (inst_tscheme (uvs, t))
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t,qs,uu____1943),None
             )
            ->
            let uu____1952 = let _0_198 = in_cur_mod env l  in _0_198 = Yes
               in
            if uu____1952
            then
              let uu____1956 =
                (FStar_All.pipe_right qs
                   (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                  || env.is_iface
                 in
              (if uu____1956 then Some (inst_tscheme (uvs, t)) else None)
            else Some (inst_tscheme (uvs, t))
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,uvs,tps,k,uu____1973,uu____1974,uu____1975,uu____1976),None
             )
            ->
            (match tps with
             | [] ->
                 let _0_200 = inst_tscheme (uvs, k)  in
                 FStar_All.pipe_left (fun _0_199  -> Some _0_199) _0_200
             | uu____2001 ->
                 let _0_204 =
                   inst_tscheme
                     (let _0_203 =
                        let _0_202 = FStar_Syntax_Syntax.mk_Total k  in
                        FStar_Syntax_Util.flat_arrow tps _0_202  in
                      (uvs, _0_203))
                    in
                 FStar_All.pipe_left (fun _0_201  -> Some _0_201) _0_204)
        | FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,uvs,tps,k,uu____2015,uu____2016,uu____2017,uu____2018),Some
             us)
            ->
            (match tps with
             | [] ->
                 let _0_206 = inst_tscheme_with (uvs, k) us  in
                 FStar_All.pipe_left (fun _0_205  -> Some _0_205) _0_206
             | uu____2044 ->
                 let _0_211 =
                   let _0_210 =
                     let _0_209 =
                       let _0_208 = FStar_Syntax_Syntax.mk_Total k  in
                       FStar_Syntax_Util.flat_arrow tps _0_208  in
                     (uvs, _0_209)  in
                   inst_tscheme_with _0_210 us  in
                 FStar_All.pipe_left (fun _0_207  -> Some _0_207) _0_211)
        | FStar_Util.Inr se ->
            (match se with
             | (FStar_Syntax_Syntax.Sig_let uu____2066,None ) ->
                 lookup_type_of_let (Prims.fst se) lid
             | uu____2077 -> effect_signature (Prims.fst se))
         in
      let uu____2082 =
        let _0_212 = lookup_qname env lid  in
        FStar_Util.bind_opt _0_212 mapper  in
      match uu____2082 with
      | Some (us,t) ->
          Some
            (us,
              (let uu___111_2110 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___111_2110.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.tk =
                   (uu___111_2110.FStar_Syntax_Syntax.tk);
                 FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                 FStar_Syntax_Syntax.vars =
                   (uu___111_2110.FStar_Syntax_Syntax.vars)
               }))
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2127 = lookup_qname env l  in
      match uu____2127 with | None  -> false | Some uu____2143 -> true
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun bv  ->
      let uu____2164 = try_lookup_bv env bv  in
      match uu____2164 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_214 = variable_not_found bv  in
                let _0_213 = FStar_Syntax_Syntax.range_of_bv bv  in
                (_0_214, _0_213)))
      | Some t ->
          let _0_215 = FStar_Syntax_Syntax.range_of_bv bv  in
          FStar_Syntax_Subst.set_use_range _0_215 t
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option
  =
  fun env  ->
    fun l  ->
      let uu____2184 = try_lookup_lid_aux env l  in
      match uu____2184 with
      | None  -> None
      | Some (us,t) ->
          Some
            (let _0_216 =
               FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l)
                 t
                in
             (us, _0_216))
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun l  ->
      let uu____2219 = try_lookup_lid env l  in
      match uu____2219 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_217 = name_not_found l  in
                (_0_217, (FStar_Ident.range_of_lid l))))
      | Some (us,t) -> (us, t)
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___97_2240  ->
              match uu___97_2240 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2242 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) Prims.option
  =
  fun env  ->
    fun lid  ->
      let uu____2253 = lookup_qname env lid  in
      match uu____2253 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2266,uvs,t,q,uu____2270),None ))
          ->
          Some
            (let _0_219 =
               let _0_218 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid lid) t
                  in
               (uvs, _0_218)  in
             (_0_219, q))
      | uu____2294 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2314 = lookup_qname env lid  in
      match uu____2314 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2325,uvs,t,uu____2328,uu____2329),None ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2345 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_220 = name_not_found lid  in
                (_0_220, (FStar_Ident.range_of_lid lid))))
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____2364 = lookup_qname env lid  in
      match uu____2364 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2375,uvs,t,uu____2378,uu____2379,uu____2380,uu____2381,uu____2382),None
           ))
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____2400 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_221 = name_not_found lid  in
                (_0_221, (FStar_Ident.range_of_lid lid))))
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____2420 = lookup_qname env lid  in
      match uu____2420 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____2432,uu____2433,uu____2434,uu____2435,uu____2436,dcs,uu____2438,uu____2439),uu____2440))
          -> (true, dcs)
      | uu____2462 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____2478 = lookup_qname env lid  in
      match uu____2478 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____2487,uu____2488,uu____2489,l,uu____2491,uu____2492,uu____2493,uu____2494),uu____2495))
          -> l
      | uu____2514 ->
          failwith
            (let _0_222 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format1 "Not a datacon: %s" _0_222)
  
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
        let uu____2546 = lookup_qname env lid  in
        match uu____2546 with
        | Some (FStar_Util.Inr (se,None )) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____2575,lbs),uu____2577,uu____2578,quals,uu____2580)
                 when visible quals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____2597 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____2597
                      then
                        Some
                          (let _0_224 =
                             let _0_223 =
                               FStar_Syntax_Util.unascribe
                                 lb.FStar_Syntax_Syntax.lbdef
                                in
                             FStar_Syntax_Subst.set_use_range
                               (FStar_Ident.range_of_lid lid) _0_223
                              in
                           ((lb.FStar_Syntax_Syntax.lbunivs), _0_224))
                      else None)
             | uu____2610 -> None)
        | uu____2613 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  ->
    fun ftv  ->
      let uu____2632 = lookup_qname env ftv  in
      match uu____2632 with
      | Some (FStar_Util.Inr (se,None )) ->
          let uu____2656 = effect_signature se  in
          (match uu____2656 with
           | None  -> None
           | Some (uu____2663,t) ->
               Some
                 (FStar_Syntax_Subst.set_use_range
                    (FStar_Ident.range_of_lid ftv) t))
      | uu____2667 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____2682 = try_lookup_effect_lid env ftv  in
      match uu____2682 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_225 = name_not_found ftv  in
                (_0_225, (FStar_Ident.range_of_lid ftv))))
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
        let uu____2697 = lookup_qname env lid0  in
        match uu____2697 with
        | Some (FStar_Util.Inr
            (FStar_Syntax_Syntax.Sig_effect_abbrev
             (lid,univs,binders,c,quals,uu____2714,uu____2715),None ))
            ->
            let lid =
              let _0_226 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid _0_226  in
            let uu____2734 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___98_2736  ->
                      match uu___98_2736 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____2737 -> false))
               in
            if uu____2734
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
                       (let _0_228 = FStar_Syntax_Print.lid_to_string lid  in
                        let _0_227 =
                          FStar_All.pipe_right (FStar_List.length univ_insts)
                            FStar_Util.string_of_int
                           in
                        FStar_Util.format2
                          "Unexpected instantiation of effect %s with %s universes"
                          _0_228 _0_227)
                  in
               match (binders, univs) with
               | ([],uu____2758) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____2767,uu____2768::uu____2769::uu____2770) when
                   Prims.op_Negation
                     (FStar_Ident.lid_equals lid
                        FStar_Syntax_Const.effect_Lemma_lid)
                   ->
                   failwith
                     (let _0_230 = FStar_Syntax_Print.lid_to_string lid  in
                      let _0_229 =
                        FStar_All.pipe_left FStar_Util.string_of_int
                          (FStar_List.length univs)
                         in
                      FStar_Util.format2
                        "Unexpected effect abbreviation %s; polymorphic in %s universes"
                        _0_230 _0_229)
               | uu____2778 ->
                   let uu____2781 =
                     let _0_232 =
                       let _0_231 = FStar_Syntax_Util.arrow binders c  in
                       (univs, _0_231)  in
                     inst_tscheme_with _0_232 insts  in
                   (match uu____2781 with
                    | (uu____2789,t) ->
                        let t =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid) t
                           in
                        let uu____2792 =
                          (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
                           in
                        (match uu____2792 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                             Some (binders, c)
                         | uu____2820 -> failwith "Impossible")))
        | uu____2824 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find l =
        let uu____2848 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l  in
        match uu____2848 with
        | None  -> None
        | Some (uu____2855,c) ->
            let l = FStar_Syntax_Util.comp_effect_name c  in
            let uu____2860 = find l  in
            (match uu____2860 with | None  -> Some l | Some l' -> Some l')
         in
      let res =
        let uu____2865 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____2865 with
        | Some l -> l
        | None  ->
            let uu____2868 = find l  in
            (match uu____2868 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l = norm_eff_name env l  in
      let uu____2880 = lookup_qname env l  in
      match uu____2880 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_new_effect (ne,uu____2891),uu____2892)) ->
          ne.FStar_Syntax_Syntax.qualifiers
      | uu____2907 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____2928 =
          failwith
            (let _0_234 = FStar_Util.string_of_int i  in
             let _0_233 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Impossible: projecting field #%s from constructor %s is undefined"
               _0_234 _0_233)
           in
        let uu____2929 = lookup_datacon env lid  in
        match uu____2929 with
        | (uu____2932,t) ->
            let uu____2934 =
              (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
            (match uu____2934 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2936) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let _0_235 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (Prims.fst b) i
                       in
                    FStar_All.pipe_right _0_235 Prims.fst)
             | uu____2959 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2966 = lookup_qname env l  in
      match uu____2966 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_declare_typ
           (uu____2975,uu____2976,uu____2977,quals,uu____2979),uu____2980))
          ->
          FStar_Util.for_some
            (fun uu___99_2997  ->
               match uu___99_2997 with
               | FStar_Syntax_Syntax.Projector uu____2998 -> true
               | uu____3001 -> false) quals
      | uu____3002 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3017 = lookup_qname env lid  in
      match uu____3017 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_datacon
           (uu____3026,uu____3027,uu____3028,uu____3029,uu____3030,uu____3031,uu____3032,uu____3033),uu____3034))
          -> true
      | uu____3053 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3068 = lookup_qname env lid  in
      match uu____3068 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3077,uu____3078,uu____3079,uu____3080,uu____3081,uu____3082,tags,uu____3084),uu____3085))
          ->
          FStar_Util.for_some
            (fun uu___100_3106  ->
               match uu___100_3106 with
               | FStar_Syntax_Syntax.RecordType _
                 |FStar_Syntax_Syntax.RecordConstructor _ -> true
               | uu____3109 -> false) tags
      | uu____3110 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3125 = lookup_qname env lid  in
      match uu____3125 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_let
           (uu____3134,uu____3135,uu____3136,tags,uu____3138),uu____3139))
          ->
          FStar_Util.for_some
            (fun uu___101_3160  ->
               match uu___101_3160 with
               | FStar_Syntax_Syntax.Action uu____3161 -> true
               | uu____3162 -> false) tags
      | uu____3163 -> false
  
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
      let uu____3180 =
        (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n  in
      match uu____3180 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____3182 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper uu___102_3200 =
        match uu___102_3200 with
        | FStar_Util.Inl uu____3209 -> Some false
        | FStar_Util.Inr (se,uu____3218) ->
            (match se with
             | FStar_Syntax_Syntax.Sig_declare_typ
                 (uu____3227,uu____3228,uu____3229,qs,uu____3231) ->
                 Some (FStar_List.contains FStar_Syntax_Syntax.New qs)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____3234 -> Some true
             | uu____3246 -> Some false)
         in
      let uu____3247 =
        let _0_236 = lookup_qname env lid  in
        FStar_Util.bind_opt _0_236 mapper  in
      match uu____3247 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____3263 = lookup_qname env lid  in
      match uu____3263 with
      | Some (FStar_Util.Inr
          (FStar_Syntax_Syntax.Sig_inductive_typ
           (uu____3272,uu____3273,tps,uu____3275,uu____3276,uu____3277,uu____3278,uu____3279),uu____3280))
          -> FStar_List.length tps
      | uu____3304 ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_237 = name_not_found lid  in
                (_0_237, (FStar_Ident.range_of_lid lid))))
  
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
      let uu____3329 = effect_decl_opt env l  in
      match uu____3329 with
      | None  ->
          Prims.raise
            (FStar_Errors.Error
               (let _0_238 = name_not_found l  in
                (_0_238, (FStar_Ident.range_of_lid l))))
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
            (let uu____3366 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____3390  ->
                       match uu____3390 with
                       | (m1,m2,uu____3398,uu____3399,uu____3400) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____3366 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      (let _0_241 =
                         let _0_240 = FStar_Syntax_Print.lid_to_string l1  in
                         let _0_239 = FStar_Syntax_Print.lid_to_string l2  in
                         FStar_Util.format2
                           "Effects %s and %s cannot be composed" _0_240
                           _0_239
                          in
                       (_0_241, (env.range))))
             | Some (uu____3412,uu____3413,m3,j1,j2) -> (m3, j1, j2))
  
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
      let uu____3450 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun d  -> FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____3450 with
      | None  ->
          failwith
            (FStar_Util.format1
               "Impossible: declaration for monad %s not found"
               m.FStar_Ident.str)
      | Some md ->
          let uu____3464 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____3464 with
           | (uu____3471,s) ->
               let s = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____3479)::(wp,uu____3481)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____3503 -> failwith "Impossible"))
  
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
              (let eff_name = norm_eff_name env eff_name  in
               let ed = get_effect_decl env eff_name  in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp
                  in
               let null_wp_res =
                 let _0_244 = get_range env  in
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app
                       (let _0_243 =
                          let _0_242 = FStar_Syntax_Syntax.as_arg res_t  in
                          [_0_242]  in
                        (null_wp, _0_243)))) None _0_244
                  in
               FStar_Syntax_Syntax.mk_Comp
                 (let _0_246 =
                    let _0_245 = FStar_Syntax_Syntax.as_arg null_wp_res  in
                    [_0_245]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = _0_246;
                    FStar_Syntax_Syntax.flags = []
                  }))
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se with
      | FStar_Syntax_Syntax.Sig_new_effect (ne,uu____3554) ->
          let effects =
            let uu___112_3556 = env.effects  in
            {
              decls = (ne :: ((env.effects).decls));
              order = (uu___112_3556.order);
              joins = (uu___112_3556.joins)
            }  in
          let uu___113_3557 = env  in
          {
            solver = (uu___113_3557.solver);
            range = (uu___113_3557.range);
            curmodule = (uu___113_3557.curmodule);
            gamma = (uu___113_3557.gamma);
            gamma_cache = (uu___113_3557.gamma_cache);
            modules = (uu___113_3557.modules);
            expected_typ = (uu___113_3557.expected_typ);
            sigtab = (uu___113_3557.sigtab);
            is_pattern = (uu___113_3557.is_pattern);
            instantiate_imp = (uu___113_3557.instantiate_imp);
            effects;
            generalize = (uu___113_3557.generalize);
            letrecs = (uu___113_3557.letrecs);
            top_level = (uu___113_3557.top_level);
            check_uvars = (uu___113_3557.check_uvars);
            use_eq = (uu___113_3557.use_eq);
            is_iface = (uu___113_3557.is_iface);
            admit = (uu___113_3557.admit);
            lax = (uu___113_3557.lax);
            lax_universes = (uu___113_3557.lax_universes);
            type_of = (uu___113_3557.type_of);
            universe_of = (uu___113_3557.universe_of);
            use_bv_sorts = (uu___113_3557.use_bv_sorts);
            qname_and_index = (uu___113_3557.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect (sub,uu____3559) ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let _0_247 = (e1.mlift).mlift_wp r wp1  in
                (e2.mlift).mlift_wp r _0_247  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let _0_249 = (e1.mlift).mlift_wp t wp  in
                              let _0_248 = l1 t wp e  in l2 t _0_249 _0_248))
                | uu____3653 -> None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t r wp1 =
            let uu____3688 = inst_tscheme lift_t  in
            match uu____3688 with
            | (uu____3693,lift_t) ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app
                      (let _0_253 =
                         let _0_252 = FStar_Syntax_Syntax.as_arg r  in
                         let _0_251 =
                           let _0_250 = FStar_Syntax_Syntax.as_arg wp1  in
                           [_0_250]  in
                         _0_252 :: _0_251  in
                       (lift_t, _0_253)))) None wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t r wp1 e =
            let uu____3739 = inst_tscheme lift_t  in
            match uu____3739 with
            | (uu____3744,lift_t) ->
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app
                      (let _0_259 =
                         let _0_258 = FStar_Syntax_Syntax.as_arg r  in
                         let _0_257 =
                           let _0_256 = FStar_Syntax_Syntax.as_arg wp1  in
                           let _0_255 =
                             let _0_254 = FStar_Syntax_Syntax.as_arg e  in
                             [_0_254]  in
                           _0_256 :: _0_255  in
                         _0_258 :: _0_257  in
                       (lift_t, _0_259)))) None e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub.FStar_Syntax_Syntax.lift mk_mlift_term  in
          let edge =
            {
              msource = (sub.FStar_Syntax_Syntax.source);
              mtarget = (sub.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub.FStar_Syntax_Syntax.source);
              mtarget = (sub.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              FStar_Syntax_Syntax.fv_to_tm
                (let _0_260 =
                   FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                 FStar_Syntax_Syntax.lid_as_fv _0_260
                   FStar_Syntax_Syntax.Delta_constant None)
               in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let _0_263 =
              FStar_Syntax_Print.term_to_string (l.mlift_wp arg wp)  in
            let _0_262 =
              let _0_261 =
                FStar_Util.map_opt l.mlift_term
                  (fun l  -> FStar_Syntax_Print.term_to_string (l arg wp e))
                 in
              FStar_Util.dflt "none" _0_261  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" _0_263 _0_262  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map (fun e  -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order uu____3819 =
            match uu____3819 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_264  -> Some _0_264)
                else
                  FStar_All.pipe_right order
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order =
            let fold_fun order k =
              let _0_268 =
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
                                    (let uu____3854 =
                                       let _0_266 = find_edge order (i, k)
                                          in
                                       let _0_265 = find_edge order (k, j)
                                          in
                                       (_0_266, _0_265)  in
                                     match uu____3854 with
                                     | (Some e1,Some e2) ->
                                         let _0_267 = compose_edges e1 e2  in
                                         [_0_267]
                                     | uu____3866 -> [])))))
                 in
              FStar_List.append order _0_268  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order
             in
          (FStar_All.pipe_right order
             (FStar_List.iter
                (fun edge  ->
                   let uu____3881 =
                     (FStar_Ident.lid_equals edge.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let _0_269 = lookup_effect_quals env edge.mtarget  in
                        FStar_All.pipe_right _0_269
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____3881
                   then
                     Prims.raise
                       (FStar_Errors.Error
                          (let _0_271 =
                             FStar_Util.format1
                               "Divergent computations cannot be included in an effect %s marked 'total'"
                               (edge.mtarget).FStar_Ident.str
                              in
                           let _0_270 = get_range env  in (_0_271, _0_270)))
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
                                            let uu____3945 =
                                              let _0_273 =
                                                find_edge order (i, k)  in
                                              let _0_272 =
                                                find_edge order (j, k)  in
                                              (_0_273, _0_272)  in
                                            match uu____3945 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____3971,uu____3972)
                                                     ->
                                                     let uu____3976 =
                                                       let _0_275 =
                                                         FStar_Util.is_some
                                                           (find_edge order
                                                              (k, ub))
                                                          in
                                                       let _0_274 =
                                                         FStar_Util.is_some
                                                           (find_edge order
                                                              (ub, k))
                                                          in
                                                       (_0_275, _0_274)  in
                                                     (match uu____3976 with
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
                                            | uu____3996 -> bopt) None)
                                 in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___114_4035 = env.effects  in
              { decls = (uu___114_4035.decls); order; joins }  in
            let uu___115_4036 = env  in
            {
              solver = (uu___115_4036.solver);
              range = (uu___115_4036.range);
              curmodule = (uu___115_4036.curmodule);
              gamma = (uu___115_4036.gamma);
              gamma_cache = (uu___115_4036.gamma_cache);
              modules = (uu___115_4036.modules);
              expected_typ = (uu___115_4036.expected_typ);
              sigtab = (uu___115_4036.sigtab);
              is_pattern = (uu___115_4036.is_pattern);
              instantiate_imp = (uu___115_4036.instantiate_imp);
              effects;
              generalize = (uu___115_4036.generalize);
              letrecs = (uu___115_4036.letrecs);
              top_level = (uu___115_4036.top_level);
              check_uvars = (uu___115_4036.check_uvars);
              use_eq = (uu___115_4036.use_eq);
              is_iface = (uu___115_4036.is_iface);
              admit = (uu___115_4036.admit);
              lax = (uu___115_4036.lax);
              lax_universes = (uu___115_4036.lax_universes);
              type_of = (uu___115_4036.type_of);
              universe_of = (uu___115_4036.universe_of);
              use_bv_sorts = (uu___115_4036.use_bv_sorts);
              qname_and_index = (uu___115_4036.qname_and_index)
            }))
      | uu____4037 -> env
  
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
        | uu____4059 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____4067 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____4067 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____4077 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____4077 with
           | (binders,cdef) ->
               (if
                  (FStar_List.length binders) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_279 =
                          let _0_278 =
                            FStar_Util.string_of_int
                              (FStar_List.length binders)
                             in
                          let _0_277 =
                            FStar_Util.string_of_int
                              ((FStar_List.length
                                  c.FStar_Syntax_Syntax.effect_args)
                                 + (Prims.parse_int "1"))
                             in
                          let _0_276 =
                            FStar_Syntax_Print.comp_to_string
                              (FStar_Syntax_Syntax.mk_Comp c)
                             in
                          FStar_Util.format3
                            "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                            _0_278 _0_277 _0_276
                           in
                        (_0_279, (comp.FStar_Syntax_Syntax.pos))))
                else ();
                (let inst =
                   let _0_281 =
                     let _0_280 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     _0_280 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____4115  ->
                        fun uu____4116  ->
                          match (uu____4115, uu____4116) with
                          | ((x,uu____4130),(t,uu____4132)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders _0_281
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef  in
                 let c =
                   let _0_282 =
                     let uu___116_4147 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___116_4147.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___116_4147.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___116_4147.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___116_4147.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right _0_282 FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c)))
  
let effect_repr_aux only_reifiable env c u_c =
  let uu____4177 =
    let _0_283 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
    effect_decl_opt env _0_283  in
  match uu____4177 with
  | None  -> None
  | Some ed ->
      let uu____4185 =
        only_reifiable &&
          (Prims.op_Negation
             (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))
         in
      if uu____4185
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____4198 ->
             let c = unfold_effect_abbrev env c  in
             let uu____4200 =
               let _0_284 = FStar_List.hd c.FStar_Syntax_Syntax.effect_args
                  in
               ((c.FStar_Syntax_Syntax.result_typ), _0_284)  in
             (match uu____4200 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr))
                     in
                  Some
                    (let _0_287 = get_range env  in
                     (FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_app
                           (let _0_286 =
                              let _0_285 = FStar_Syntax_Syntax.as_arg res_typ
                                 in
                              [_0_285; wp]  in
                            (repr, _0_286)))) None _0_287)))
  
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
          Prims.raise
            (FStar_Errors.Error
               (let _0_290 =
                  let _0_288 = FStar_Ident.string_of_lid l  in
                  FStar_Util.format1 "Effect %s cannot be reified" _0_288  in
                let _0_289 = get_range env  in (_0_290, _0_289)))
           in
        let uu____4285 = effect_repr_aux true env c u_c  in
        match uu____4285 with
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
        | FStar_Util.Inr (eff_name,uu____4317) -> eff_name  in
      is_reifiable_effect env effect_lid
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____4330 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____4337 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
         in
      match uu____4337 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____4338,c) ->
          is_reifiable_comp env c
      | uu____4350 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push x rest =
        match rest with
        | (Binding_sig _)::_|(Binding_sig_inst _)::_ -> x :: rest
        | [] -> [x]
        | local::rest -> let _0_291 = push x rest  in local :: _0_291  in
      let uu___117_4375 = env  in
      let _0_292 = push s env.gamma  in
      {
        solver = (uu___117_4375.solver);
        range = (uu___117_4375.range);
        curmodule = (uu___117_4375.curmodule);
        gamma = _0_292;
        gamma_cache = (uu___117_4375.gamma_cache);
        modules = (uu___117_4375.modules);
        expected_typ = (uu___117_4375.expected_typ);
        sigtab = (uu___117_4375.sigtab);
        is_pattern = (uu___117_4375.is_pattern);
        instantiate_imp = (uu___117_4375.instantiate_imp);
        effects = (uu___117_4375.effects);
        generalize = (uu___117_4375.generalize);
        letrecs = (uu___117_4375.letrecs);
        top_level = (uu___117_4375.top_level);
        check_uvars = (uu___117_4375.check_uvars);
        use_eq = (uu___117_4375.use_eq);
        is_iface = (uu___117_4375.is_iface);
        admit = (uu___117_4375.admit);
        lax = (uu___117_4375.lax);
        lax_universes = (uu___117_4375.lax_universes);
        type_of = (uu___117_4375.type_of);
        universe_of = (uu___117_4375.universe_of);
        use_bv_sorts = (uu___117_4375.use_bv_sorts);
        qname_and_index = (uu___117_4375.qname_and_index)
      }
  
let push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env s
  
let push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env s
  
let push_local_binding : env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___118_4401 = env  in
      {
        solver = (uu___118_4401.solver);
        range = (uu___118_4401.range);
        curmodule = (uu___118_4401.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___118_4401.gamma_cache);
        modules = (uu___118_4401.modules);
        expected_typ = (uu___118_4401.expected_typ);
        sigtab = (uu___118_4401.sigtab);
        is_pattern = (uu___118_4401.is_pattern);
        instantiate_imp = (uu___118_4401.instantiate_imp);
        effects = (uu___118_4401.effects);
        generalize = (uu___118_4401.generalize);
        letrecs = (uu___118_4401.letrecs);
        top_level = (uu___118_4401.top_level);
        check_uvars = (uu___118_4401.check_uvars);
        use_eq = (uu___118_4401.use_eq);
        is_iface = (uu___118_4401.is_iface);
        admit = (uu___118_4401.admit);
        lax = (uu___118_4401.lax);
        lax_universes = (uu___118_4401.lax_universes);
        type_of = (uu___118_4401.type_of);
        universe_of = (uu___118_4401.universe_of);
        use_bv_sorts = (uu___118_4401.use_bv_sorts);
        qname_and_index = (uu___118_4401.qname_and_index)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env  ->
           fun uu____4417  ->
             match uu____4417 with | (x,uu____4421) -> push_bv env x) env bs
  
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
            let uu___119_4441 = x  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___119_4441.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___119_4441.FStar_Syntax_Syntax.index);
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
      (let uu___120_4471 = env  in
       {
         solver = (uu___120_4471.solver);
         range = (uu___120_4471.range);
         curmodule = (uu___120_4471.curmodule);
         gamma = [];
         gamma_cache = (uu___120_4471.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___120_4471.sigtab);
         is_pattern = (uu___120_4471.is_pattern);
         instantiate_imp = (uu___120_4471.instantiate_imp);
         effects = (uu___120_4471.effects);
         generalize = (uu___120_4471.generalize);
         letrecs = (uu___120_4471.letrecs);
         top_level = (uu___120_4471.top_level);
         check_uvars = (uu___120_4471.check_uvars);
         use_eq = (uu___120_4471.use_eq);
         is_iface = (uu___120_4471.is_iface);
         admit = (uu___120_4471.admit);
         lax = (uu___120_4471.lax);
         lax_universes = (uu___120_4471.lax_universes);
         type_of = (uu___120_4471.type_of);
         universe_of = (uu___120_4471.universe_of);
         use_bv_sorts = (uu___120_4471.use_bv_sorts);
         qname_and_index = (uu___120_4471.qname_and_index)
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
      let uu___121_4486 = env  in
      {
        solver = (uu___121_4486.solver);
        range = (uu___121_4486.range);
        curmodule = (uu___121_4486.curmodule);
        gamma = (uu___121_4486.gamma);
        gamma_cache = (uu___121_4486.gamma_cache);
        modules = (uu___121_4486.modules);
        expected_typ = (Some t);
        sigtab = (uu___121_4486.sigtab);
        is_pattern = (uu___121_4486.is_pattern);
        instantiate_imp = (uu___121_4486.instantiate_imp);
        effects = (uu___121_4486.effects);
        generalize = (uu___121_4486.generalize);
        letrecs = (uu___121_4486.letrecs);
        top_level = (uu___121_4486.top_level);
        check_uvars = (uu___121_4486.check_uvars);
        use_eq = false;
        is_iface = (uu___121_4486.is_iface);
        admit = (uu___121_4486.admit);
        lax = (uu___121_4486.lax);
        lax_universes = (uu___121_4486.lax_universes);
        type_of = (uu___121_4486.type_of);
        universe_of = (uu___121_4486.universe_of);
        use_bv_sorts = (uu___121_4486.use_bv_sorts);
        qname_and_index = (uu___121_4486.qname_and_index)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ Prims.option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ Prims.option)
  =
  fun env_  ->
    let _0_293 = expected_typ env_  in
    ((let uu___122_4503 = env_  in
      {
        solver = (uu___122_4503.solver);
        range = (uu___122_4503.range);
        curmodule = (uu___122_4503.curmodule);
        gamma = (uu___122_4503.gamma);
        gamma_cache = (uu___122_4503.gamma_cache);
        modules = (uu___122_4503.modules);
        expected_typ = None;
        sigtab = (uu___122_4503.sigtab);
        is_pattern = (uu___122_4503.is_pattern);
        instantiate_imp = (uu___122_4503.instantiate_imp);
        effects = (uu___122_4503.effects);
        generalize = (uu___122_4503.generalize);
        letrecs = (uu___122_4503.letrecs);
        top_level = (uu___122_4503.top_level);
        check_uvars = (uu___122_4503.check_uvars);
        use_eq = false;
        is_iface = (uu___122_4503.is_iface);
        admit = (uu___122_4503.admit);
        lax = (uu___122_4503.lax);
        lax_universes = (uu___122_4503.lax_universes);
        type_of = (uu___122_4503.type_of);
        universe_of = (uu___122_4503.universe_of);
        use_bv_sorts = (uu___122_4503.use_bv_sorts);
        qname_and_index = (uu___122_4503.qname_and_index)
      }), _0_293)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let _0_294 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___103_4518  ->
                    match uu___103_4518 with
                    | Binding_sig (uu____4520,se) -> [se]
                    | uu____4524 -> []))
             in
          FStar_All.pipe_right _0_294 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___123_4527 = env  in
       {
         solver = (uu___123_4527.solver);
         range = (uu___123_4527.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___123_4527.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___123_4527.expected_typ);
         sigtab = (uu___123_4527.sigtab);
         is_pattern = (uu___123_4527.is_pattern);
         instantiate_imp = (uu___123_4527.instantiate_imp);
         effects = (uu___123_4527.effects);
         generalize = (uu___123_4527.generalize);
         letrecs = (uu___123_4527.letrecs);
         top_level = (uu___123_4527.top_level);
         check_uvars = (uu___123_4527.check_uvars);
         use_eq = (uu___123_4527.use_eq);
         is_iface = (uu___123_4527.is_iface);
         admit = (uu___123_4527.admit);
         lax = (uu___123_4527.lax);
         lax_universes = (uu___123_4527.lax_universes);
         type_of = (uu___123_4527.type_of);
         universe_of = (uu___123_4527.universe_of);
         use_bv_sorts = (uu___123_4527.use_bv_sorts);
         qname_and_index = (uu___123_4527.qname_and_index)
       })
  
let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs = FStar_Syntax_Syntax.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____4577)::tl -> aux out tl
      | (Binding_lid (_,(_,t)))::tl|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl ->
          let _0_296 =
            let _0_295 = FStar_Syntax_Free.uvars t  in ext out _0_295  in
          aux _0_296 tl
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
          let _0_298 =
            let _0_297 = FStar_Syntax_Free.univs t  in ext out _0_297  in
          aux _0_298 tl
      | (Binding_sig uu____4644)::uu____4645 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____4682)::tl -> aux out tl
      | (Binding_univ uname)::tl ->
          let _0_299 = FStar_Util.set_add uname out  in aux _0_299 tl
      | (Binding_lid (_,(_,t)))::tl|(Binding_var
        { FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_})::tl ->
          let _0_301 =
            let _0_300 = FStar_Syntax_Free.univnames t  in ext out _0_300  in
          aux _0_301 tl
      | (Binding_sig uu____4704)::uu____4705 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___104_4721  ->
            match uu___104_4721 with
            | Binding_var x -> [x]
            | Binding_lid _|Binding_sig _|Binding_univ _|Binding_sig_inst _
                -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let _0_303 =
      let _0_302 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right _0_302
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right _0_303 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a  -> f a e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___105_4782  ->
             match uu___105_4782 with
             | Binding_sig (lids,uu____4786) -> FStar_List.append lids keys
             | uu____4789 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____4791  ->
         fun v  ->
           fun keys  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)
      keys
  
let dummy_solver : solver_t =
  {
    init = (fun uu____4795  -> ());
    push = (fun uu____4796  -> ());
    pop = (fun uu____4797  -> ());
    mark = (fun uu____4798  -> ());
    reset_mark = (fun uu____4799  -> ());
    commit_mark = (fun uu____4800  -> ());
    encode_modul = (fun uu____4801  -> fun uu____4802  -> ());
    encode_sig = (fun uu____4803  -> fun uu____4804  -> ());
    solve = (fun uu____4805  -> fun uu____4806  -> fun uu____4807  -> ());
    is_trivial = (fun uu____4811  -> fun uu____4812  -> false);
    finish = (fun uu____4813  -> ());
    refresh = (fun uu____4814  -> ())
  } 