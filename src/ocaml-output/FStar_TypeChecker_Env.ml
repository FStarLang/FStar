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
    match projectee with | Binding_var _0 -> true | uu____34 -> false
  
let __proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_lid : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____48 -> false
  
let __proj__Binding_lid__item___0 :
  binding -> (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) =
  fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let uu___is_Binding_sig : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____69 -> false
  
let __proj__Binding_sig__item___0 :
  binding -> (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) =
  fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let uu___is_Binding_univ : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____90 -> false
  
let __proj__Binding_univ__item___0 : binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let uu___is_Binding_sig_inst : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____106 -> false
  
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
  | UnfoldTac 
let uu___is_NoDelta : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____133 -> false
  
let uu___is_Inlining : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____137 -> false
  
let uu___is_Eager_unfolding_only : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____141 -> false
  
let uu___is_Unfold : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____146 -> false
  
let __proj__Unfold__item___0 : delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0 
let uu___is_UnfoldTac : delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____157 -> false
  
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
      option
    }
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list
    }
type name_prefix = Prims.string Prims.list
type flat_proof_namespace = (name_prefix * Prims.bool) Prims.list
type proof_namespace = flat_proof_namespace Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                option))
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
  expected_typ: FStar_Syntax_Syntax.typ option ;
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
  qname_and_index: (FStar_Ident.lident * Prims.int) option ;
  proof_ns: proof_namespace ;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool }
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
  preprocess:
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list ;
  solve:
    (Prims.unit -> Prims.string) option ->
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
      | (NoDelta ,uu____997) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____998,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____999,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____1000 -> false
  
let default_table_size : Prims.int = (Prims.parse_int "200") 
let new_sigtab uu____1010 = FStar_Util.smap_create default_table_size 
let new_gamma_cache uu____1018 =
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
          let uu____1057 = new_gamma_cache ()  in
          let uu____1059 = new_sigtab ()  in
          let uu____1061 =
            let uu____1062 = FStar_Options.using_facts_from ()  in
            match uu____1062 with
            | Some ns ->
                let uu____1068 =
                  let uu____1073 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns
                     in
                  FStar_List.append uu____1073 [([], false)]  in
                [uu____1068]
            | None  -> [[]]  in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____1057;
            modules = [];
            expected_typ = None;
            sigtab = uu____1059;
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
            proof_ns = uu____1061;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____1125  -> false)
          }
  
let sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab 
let gamma_cache : env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache 
let query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let push_query_indices : Prims.unit -> Prims.unit =
  fun uu____1155  ->
    let uu____1156 = FStar_ST.read query_indices  in
    match uu____1156 with
    | [] -> failwith "Empty query indices!"
    | uu____1170 ->
        let uu____1175 =
          let uu____1180 =
            let uu____1184 = FStar_ST.read query_indices  in
            FStar_List.hd uu____1184  in
          let uu____1198 = FStar_ST.read query_indices  in uu____1180 ::
            uu____1198
           in
        FStar_ST.write query_indices uu____1175
  
let pop_query_indices : Prims.unit -> Prims.unit =
  fun uu____1220  ->
    let uu____1221 = FStar_ST.read query_indices  in
    match uu____1221 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
  
let add_query_index : (FStar_Ident.lident * Prims.int) -> Prims.unit =
  fun uu____1257  ->
    match uu____1257 with
    | (l,n1) ->
        let uu____1262 = FStar_ST.read query_indices  in
        (match uu____1262 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1296 -> failwith "Empty query indices")
  
let peek_query_indices :
  Prims.unit -> (FStar_Ident.lident * Prims.int) Prims.list =
  fun uu____1306  ->
    let uu____1307 = FStar_ST.read query_indices  in FStar_List.hd uu____1307
  
let commit_query_index_mark : Prims.unit -> Prims.unit =
  fun uu____1323  ->
    let uu____1324 = FStar_ST.read query_indices  in
    match uu____1324 with
    | hd1::uu____1336::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1363 -> failwith "Unmarked query index stack"
  
let stack : env Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let push_stack : env -> env =
  fun env  ->
    (let uu____1377 =
       let uu____1379 = FStar_ST.read stack  in env :: uu____1379  in
     FStar_ST.write stack uu____1377);
    (let uu___114_1387 = env  in
     let uu____1388 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____1390 = FStar_Util.smap_copy (sigtab env)  in
     {
       solver = (uu___114_1387.solver);
       range = (uu___114_1387.range);
       curmodule = (uu___114_1387.curmodule);
       gamma = (uu___114_1387.gamma);
       gamma_cache = uu____1388;
       modules = (uu___114_1387.modules);
       expected_typ = (uu___114_1387.expected_typ);
       sigtab = uu____1390;
       is_pattern = (uu___114_1387.is_pattern);
       instantiate_imp = (uu___114_1387.instantiate_imp);
       effects = (uu___114_1387.effects);
       generalize = (uu___114_1387.generalize);
       letrecs = (uu___114_1387.letrecs);
       top_level = (uu___114_1387.top_level);
       check_uvars = (uu___114_1387.check_uvars);
       use_eq = (uu___114_1387.use_eq);
       is_iface = (uu___114_1387.is_iface);
       admit = (uu___114_1387.admit);
       lax = (uu___114_1387.lax);
       lax_universes = (uu___114_1387.lax_universes);
       type_of = (uu___114_1387.type_of);
       universe_of = (uu___114_1387.universe_of);
       use_bv_sorts = (uu___114_1387.use_bv_sorts);
       qname_and_index = (uu___114_1387.qname_and_index);
       proof_ns = (uu___114_1387.proof_ns);
       synth = (uu___114_1387.synth);
       is_native_tactic = (uu___114_1387.is_native_tactic)
     })
  
let pop_stack : Prims.unit -> env =
  fun uu____1394  ->
    let uu____1395 = FStar_ST.read stack  in
    match uu____1395 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1407 -> failwith "Impossible: Too many pops"
  
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
    (let uu____1439 = pop_stack ()  in ());
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
        let uu____1458 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1470  ->
                  match uu____1470 with
                  | (m,uu____1474) -> FStar_Ident.lid_equals l m))
           in
        (match uu____1458 with
         | None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___115_1479 = env  in
               {
                 solver = (uu___115_1479.solver);
                 range = (uu___115_1479.range);
                 curmodule = (uu___115_1479.curmodule);
                 gamma = (uu___115_1479.gamma);
                 gamma_cache = (uu___115_1479.gamma_cache);
                 modules = (uu___115_1479.modules);
                 expected_typ = (uu___115_1479.expected_typ);
                 sigtab = (uu___115_1479.sigtab);
                 is_pattern = (uu___115_1479.is_pattern);
                 instantiate_imp = (uu___115_1479.instantiate_imp);
                 effects = (uu___115_1479.effects);
                 generalize = (uu___115_1479.generalize);
                 letrecs = (uu___115_1479.letrecs);
                 top_level = (uu___115_1479.top_level);
                 check_uvars = (uu___115_1479.check_uvars);
                 use_eq = (uu___115_1479.use_eq);
                 is_iface = (uu___115_1479.is_iface);
                 admit = (uu___115_1479.admit);
                 lax = (uu___115_1479.lax);
                 lax_universes = (uu___115_1479.lax_universes);
                 type_of = (uu___115_1479.type_of);
                 universe_of = (uu___115_1479.universe_of);
                 use_bv_sorts = (uu___115_1479.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___115_1479.proof_ns);
                 synth = (uu___115_1479.synth);
                 is_native_tactic = (uu___115_1479.is_native_tactic)
               }))
         | Some (uu____1482,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              (let uu___116_1488 = env  in
               {
                 solver = (uu___116_1488.solver);
                 range = (uu___116_1488.range);
                 curmodule = (uu___116_1488.curmodule);
                 gamma = (uu___116_1488.gamma);
                 gamma_cache = (uu___116_1488.gamma_cache);
                 modules = (uu___116_1488.modules);
                 expected_typ = (uu___116_1488.expected_typ);
                 sigtab = (uu___116_1488.sigtab);
                 is_pattern = (uu___116_1488.is_pattern);
                 instantiate_imp = (uu___116_1488.instantiate_imp);
                 effects = (uu___116_1488.effects);
                 generalize = (uu___116_1488.generalize);
                 letrecs = (uu___116_1488.letrecs);
                 top_level = (uu___116_1488.top_level);
                 check_uvars = (uu___116_1488.check_uvars);
                 use_eq = (uu___116_1488.use_eq);
                 is_iface = (uu___116_1488.is_iface);
                 admit = (uu___116_1488.admit);
                 lax = (uu___116_1488.lax);
                 lax_universes = (uu___116_1488.lax_universes);
                 type_of = (uu___116_1488.type_of);
                 universe_of = (uu___116_1488.universe_of);
                 use_bv_sorts = (uu___116_1488.use_bv_sorts);
                 qname_and_index = (Some (l, next));
                 proof_ns = (uu___116_1488.proof_ns);
                 synth = (uu___116_1488.synth);
                 is_native_tactic = (uu___116_1488.is_native_tactic)
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
        (let uu___117_1504 = e  in
         {
           solver = (uu___117_1504.solver);
           range = r;
           curmodule = (uu___117_1504.curmodule);
           gamma = (uu___117_1504.gamma);
           gamma_cache = (uu___117_1504.gamma_cache);
           modules = (uu___117_1504.modules);
           expected_typ = (uu___117_1504.expected_typ);
           sigtab = (uu___117_1504.sigtab);
           is_pattern = (uu___117_1504.is_pattern);
           instantiate_imp = (uu___117_1504.instantiate_imp);
           effects = (uu___117_1504.effects);
           generalize = (uu___117_1504.generalize);
           letrecs = (uu___117_1504.letrecs);
           top_level = (uu___117_1504.top_level);
           check_uvars = (uu___117_1504.check_uvars);
           use_eq = (uu___117_1504.use_eq);
           is_iface = (uu___117_1504.is_iface);
           admit = (uu___117_1504.admit);
           lax = (uu___117_1504.lax);
           lax_universes = (uu___117_1504.lax_universes);
           type_of = (uu___117_1504.type_of);
           universe_of = (uu___117_1504.universe_of);
           use_bv_sorts = (uu___117_1504.use_bv_sorts);
           qname_and_index = (uu___117_1504.qname_and_index);
           proof_ns = (uu___117_1504.proof_ns);
           synth = (uu___117_1504.synth);
           is_native_tactic = (uu___117_1504.is_native_tactic)
         })
  
let get_range : env -> FStar_Range.range = fun e  -> e.range 
let modules : env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules 
let current_module : env -> FStar_Ident.lident = fun env  -> env.curmodule 
let set_current_module : env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___118_1521 = env  in
      {
        solver = (uu___118_1521.solver);
        range = (uu___118_1521.range);
        curmodule = lid;
        gamma = (uu___118_1521.gamma);
        gamma_cache = (uu___118_1521.gamma_cache);
        modules = (uu___118_1521.modules);
        expected_typ = (uu___118_1521.expected_typ);
        sigtab = (uu___118_1521.sigtab);
        is_pattern = (uu___118_1521.is_pattern);
        instantiate_imp = (uu___118_1521.instantiate_imp);
        effects = (uu___118_1521.effects);
        generalize = (uu___118_1521.generalize);
        letrecs = (uu___118_1521.letrecs);
        top_level = (uu___118_1521.top_level);
        check_uvars = (uu___118_1521.check_uvars);
        use_eq = (uu___118_1521.use_eq);
        is_iface = (uu___118_1521.is_iface);
        admit = (uu___118_1521.admit);
        lax = (uu___118_1521.lax);
        lax_universes = (uu___118_1521.lax_universes);
        type_of = (uu___118_1521.type_of);
        universe_of = (uu___118_1521.universe_of);
        use_bv_sorts = (uu___118_1521.use_bv_sorts);
        qname_and_index = (uu___118_1521.qname_and_index);
        proof_ns = (uu___118_1521.proof_ns);
        synth = (uu___118_1521.synth);
        is_native_tactic = (uu___118_1521.is_native_tactic)
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
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.sigelt option =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
  
let name_not_found : FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str 
let variable_not_found : FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1543 = FStar_Syntax_Print.bv_to_string v1  in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1543
  
let new_u_univ : Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1546  ->
    let uu____1547 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____1547
  
let inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1569) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____1585 = FStar_Syntax_Subst.subst vs t  in (us, uu____1585)
  
let inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun uu___102_1590  ->
    match uu___102_1590 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1604  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term)
  =
  fun r  ->
    fun t  ->
      let uu____1614 = inst_tscheme t  in
      match uu____1614 with
      | (us,t1) ->
          let uu____1621 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____1621)
  
let inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1633  ->
          match uu____1633 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1647 =
                         let uu____1648 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____1651 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____1654 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____1655 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1648 uu____1651 uu____1654 uu____1655
                          in
                       failwith uu____1647)
                    else ();
                    (let uu____1657 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     snd uu____1657))
               | uu____1661 ->
                   let uu____1662 =
                     let uu____1663 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1663
                      in
                   failwith uu____1662)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let uu___is_Yes : tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1667 -> false 
let uu___is_No : tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1671 -> false 
let uu___is_Maybe : tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1675 -> false
  
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
             | ([],uu____1701) -> Maybe
             | (uu____1705,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1717 -> No  in
           aux cur1 lns)
        else No
  
let lookup_qname :
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                    *
                                                                    FStar_Syntax_Syntax.universes
                                                                    option))
        FStar_Util.either * FStar_Range.range) option
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
          let uu____1777 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____1777 with
          | None  ->
              FStar_Util.find_map env.gamma
                (fun uu___103_1798  ->
                   match uu___103_1798 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1821 =
                           let uu____1831 =
                             let uu____1839 = inst_tscheme t  in
                             FStar_Util.Inl uu____1839  in
                           (uu____1831, (FStar_Ident.range_of_lid l))  in
                         Some uu____1821
                       else None
                   | Binding_sig
                       (uu____1873,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1875);
                                     FStar_Syntax_Syntax.sigrng = uu____1876;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1877;
                                     FStar_Syntax_Syntax.sigmeta = uu____1878;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1887 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____1887
                            then
                              cache
                                ((FStar_Util.Inr (se, None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1914 ->
                             Some t
                         | uu____1918 -> cache t  in
                       let uu____1919 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____1919 with
                        | None  -> None
                        | Some l ->
                            maybe_cache
                              ((FStar_Util.Inr (s, None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1959 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____1959 with
                        | None  -> None
                        | Some l ->
                            Some
                              ((FStar_Util.Inr (s, (Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____2003 -> None)
          | se -> se
        else None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____2045 =
           (cur_mod <> Yes) || (has_interface env env.curmodule)  in
         if uu____2045
         then
           let uu____2056 = find_in_sigtab env lid  in
           match uu____2056 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2122) ->
          add_sigelts env ses
      | uu____2127 ->
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
            | uu____2136 -> ()))

and add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit
  =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Range.range) option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___104_2154  ->
           match uu___104_2154 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2167 -> None)
  
let lookup_type_of_let :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
        FStar_Range.range) option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2188,lb::[]),uu____2190,uu____2191) ->
          let uu____2200 =
            let uu____2205 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp))
               in
            let uu____2211 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname
               in
            (uu____2205, uu____2211)  in
          Some uu____2200
      | FStar_Syntax_Syntax.Sig_let ((uu____2218,lbs),uu____2220,uu____2221)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2241 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2248 = FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                   if uu____2248
                   then
                     let uu____2254 =
                       let uu____2259 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp))
                          in
                       let uu____2265 = FStar_Syntax_Syntax.range_of_fv fv
                          in
                       (uu____2259, uu____2265)  in
                     Some uu____2254
                   else None)
      | uu____2277 -> None
  
let effect_signature :
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
      FStar_Range.range) option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2296 =
          let uu____2301 =
            let uu____2304 =
              let uu____2305 =
                let uu____2308 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature
                   in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2308
                 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2305)  in
            inst_tscheme uu____2304  in
          (uu____2301, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____2296
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2322,uu____2323) ->
        let uu____2326 =
          let uu____2331 =
            let uu____2334 =
              let uu____2335 =
                let uu____2338 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                FStar_Syntax_Util.arrow binders uu____2338  in
              (us, uu____2335)  in
            inst_tscheme uu____2334  in
          (uu____2331, (se.FStar_Syntax_Syntax.sigrng))  in
        Some uu____2326
    | uu____2349 -> None
  
let try_lookup_lid_aux :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) * FStar_Range.range) option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2384 =
        match uu____2384 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2434,uvs,t,uu____2437,uu____2438,uu____2439);
                    FStar_Syntax_Syntax.sigrng = uu____2440;
                    FStar_Syntax_Syntax.sigquals = uu____2441;
                    FStar_Syntax_Syntax.sigmeta = uu____2442;_},None
                  )
                 ->
                 let uu____2452 =
                   let uu____2457 = inst_tscheme (uvs, t)  in
                   (uu____2457, rng)  in
                 Some uu____2452
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2469;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2471;_},None
                  )
                 ->
                 let uu____2479 =
                   let uu____2480 = in_cur_mod env l  in uu____2480 = Yes  in
                 if uu____2479
                 then
                   let uu____2486 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface
                      in
                   (if uu____2486
                    then
                      let uu____2493 =
                        let uu____2498 = inst_tscheme (uvs, t)  in
                        (uu____2498, rng)  in
                      Some uu____2493
                    else None)
                 else
                   (let uu____2513 =
                      let uu____2518 = inst_tscheme (uvs, t)  in
                      (uu____2518, rng)  in
                    Some uu____2513)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2531,uu____2532);
                    FStar_Syntax_Syntax.sigrng = uu____2533;
                    FStar_Syntax_Syntax.sigquals = uu____2534;
                    FStar_Syntax_Syntax.sigmeta = uu____2535;_},None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2554 =
                        let uu____2559 = inst_tscheme (uvs, k)  in
                        (uu____2559, rng)  in
                      Some uu____2554
                  | uu____2568 ->
                      let uu____2569 =
                        let uu____2574 =
                          let uu____2577 =
                            let uu____2578 =
                              let uu____2581 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____2581  in
                            (uvs, uu____2578)  in
                          inst_tscheme uu____2577  in
                        (uu____2574, rng)  in
                      Some uu____2569)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2596,uu____2597);
                    FStar_Syntax_Syntax.sigrng = uu____2598;
                    FStar_Syntax_Syntax.sigquals = uu____2599;
                    FStar_Syntax_Syntax.sigmeta = uu____2600;_},Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2620 =
                        let uu____2625 = inst_tscheme_with (uvs, k) us  in
                        (uu____2625, rng)  in
                      Some uu____2620
                  | uu____2634 ->
                      let uu____2635 =
                        let uu____2640 =
                          let uu____2643 =
                            let uu____2644 =
                              let uu____2647 = FStar_Syntax_Syntax.mk_Total k
                                 in
                              FStar_Syntax_Util.flat_arrow tps uu____2647  in
                            (uvs, uu____2644)  in
                          inst_tscheme_with uu____2643 us  in
                        (uu____2640, rng)  in
                      Some uu____2635)
             | FStar_Util.Inr se ->
                 let uu____2667 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2678;
                        FStar_Syntax_Syntax.sigrng = uu____2679;
                        FStar_Syntax_Syntax.sigquals = uu____2680;
                        FStar_Syntax_Syntax.sigmeta = uu____2681;_},None
                      ) -> lookup_type_of_let (fst se) lid
                   | uu____2690 -> effect_signature (fst se)  in
                 FStar_All.pipe_right uu____2667
                   (FStar_Util.map_option
                      (fun uu____2713  ->
                         match uu____2713 with | (us_t,rng1) -> (us_t, rng1))))
         in
      let uu____2730 =
        let uu____2736 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____2736 mapper  in
      match uu____2730 with
      | Some ((us,t),r) ->
          Some
            ((us,
               (let uu___119_2788 = t  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___119_2788.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___119_2788.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___119_2788.FStar_Syntax_Syntax.vars)
                })), r)
      | None  -> None
  
let lid_exists : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2809 = lookup_qname env l  in
      match uu____2809 with | None  -> false | Some uu____2829 -> true
  
let lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____2857 = try_lookup_bv env bv  in
      match uu____2857 with
      | None  ->
          let uu____2865 =
            let uu____2866 =
              let uu____2869 = variable_not_found bv  in (uu____2869, bvr)
               in
            FStar_Errors.Error uu____2866  in
          raise uu____2865
      | Some (t,r) ->
          let uu____2876 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____2877 = FStar_Range.set_use_range r bvr  in
          (uu____2876, uu____2877)
  
let try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) option
  =
  fun env  ->
    fun l  ->
      let uu____2889 = try_lookup_lid_aux env l  in
      match uu____2889 with
      | None  -> None
      | Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 = FStar_Range.set_use_range r use_range  in
          let uu____2931 =
            let uu____2936 =
              let uu____2939 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____2939)  in
            (uu____2936, r1)  in
          Some uu____2931
  
let lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range)
  =
  fun env  ->
    fun l  ->
      let uu____2956 = try_lookup_lid env l  in
      match uu____2956 with
      | None  ->
          let uu____2970 =
            let uu____2971 =
              let uu____2974 = name_not_found l  in
              (uu____2974, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____2971  in
          raise uu____2970
      | Some v1 -> v1
  
let lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___105_2995  ->
              match uu___105_2995 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2997 -> false) env.gamma) FStar_Option.isSome
  
let try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun lid  ->
      let uu____3008 = lookup_qname env lid  in
      match uu____3008 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3023,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3026;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3028;_},None
            ),uu____3029)
          ->
          let uu____3053 =
            let uu____3059 =
              let uu____3062 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t
                 in
              (uvs, uu____3062)  in
            (uu____3059, q)  in
          Some uu____3053
      | uu____3071 -> None
  
let lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3093 = lookup_qname env lid  in
      match uu____3093 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3106,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____3109;
              FStar_Syntax_Syntax.sigquals = uu____3110;
              FStar_Syntax_Syntax.sigmeta = uu____3111;_},None
            ),uu____3112)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3136 ->
          let uu____3147 =
            let uu____3148 =
              let uu____3151 = name_not_found lid  in
              (uu____3151, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3148  in
          raise uu____3147
  
let lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun lid  ->
      let uu____3162 = lookup_qname env lid  in
      match uu____3162 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3175,uvs,t,uu____3178,uu____3179,uu____3180);
              FStar_Syntax_Syntax.sigrng = uu____3181;
              FStar_Syntax_Syntax.sigquals = uu____3182;
              FStar_Syntax_Syntax.sigmeta = uu____3183;_},None
            ),uu____3184)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3210 ->
          let uu____3221 =
            let uu____3222 =
              let uu____3225 = name_not_found lid  in
              (uu____3225, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____3222  in
          raise uu____3221
  
let datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____3237 = lookup_qname env lid  in
      match uu____3237 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3251,uu____3252,uu____3253,uu____3254,uu____3255,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3257;
              FStar_Syntax_Syntax.sigquals = uu____3258;
              FStar_Syntax_Syntax.sigmeta = uu____3259;_},uu____3260),uu____3261)
          -> (true, dcs)
      | uu____3291 -> (false, [])
  
let typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3309 = lookup_qname env lid  in
      match uu____3309 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3320,uu____3321,uu____3322,l,uu____3324,uu____3325);
              FStar_Syntax_Syntax.sigrng = uu____3326;
              FStar_Syntax_Syntax.sigquals = uu____3327;
              FStar_Syntax_Syntax.sigmeta = uu____3328;_},uu____3329),uu____3330)
          -> l
      | uu____3357 ->
          let uu____3368 =
            let uu____3369 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____3369  in
          failwith uu____3368
  
let lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) option
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
        let uu____3393 = lookup_qname env lid  in
        match uu____3393 with
        | Some (FStar_Util.Inr (se,None ),uu____3408) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3434,lbs),uu____3436,uu____3437) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____3454 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____3454
                      then
                        Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else None)
             | uu____3475 -> None)
        | uu____3478 -> None
  
let try_lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ option =
  fun env  ->
    fun ftv  ->
      let uu____3499 = lookup_qname env ftv  in
      match uu____3499 with
      | Some (FStar_Util.Inr (se,None ),uu____3512) ->
          let uu____3535 = effect_signature se  in
          (match uu____3535 with
           | None  -> None
           | Some ((uu____3546,t),r) ->
               let uu____3555 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t
                  in
               Some uu____3555)
      | uu____3556 -> None
  
let lookup_effect_lid : env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun ftv  ->
      let uu____3573 = try_lookup_effect_lid env ftv  in
      match uu____3573 with
      | None  ->
          let uu____3575 =
            let uu____3576 =
              let uu____3579 = name_not_found ftv  in
              (uu____3579, (FStar_Ident.range_of_lid ftv))  in
            FStar_Errors.Error uu____3576  in
          raise uu____3575
      | Some k -> k
  
let lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3593 = lookup_qname env lid0  in
        match uu____3593 with
        | Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3611);
                FStar_Syntax_Syntax.sigrng = uu____3612;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3614;_},None
              ),uu____3615)
            ->
            let lid1 =
              let uu____3642 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0)
                 in
              FStar_Ident.set_lid_range lid uu____3642  in
            let uu____3643 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___106_3645  ->
                      match uu___106_3645 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3646 -> false))
               in
            if uu____3643
            then None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3659 =
                      let uu____3660 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____3661 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3660 uu____3661
                       in
                    failwith uu____3659)
                  in
               match (binders, univs1) with
               | ([],uu____3667) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3676,uu____3677::uu____3678::uu____3679) ->
                   let uu____3682 =
                     let uu____3683 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____3684 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3683 uu____3684
                      in
                   failwith uu____3682
               | uu____3690 ->
                   let uu____3693 =
                     let uu____3696 =
                       let uu____3697 = FStar_Syntax_Util.arrow binders c  in
                       (univs1, uu____3697)  in
                     inst_tscheme_with uu____3696 insts  in
                   (match uu____3693 with
                    | (uu____3705,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t
                           in
                        let uu____3708 =
                          let uu____3709 = FStar_Syntax_Subst.compress t1  in
                          uu____3709.FStar_Syntax_Syntax.n  in
                        (match uu____3708 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             Some (binders1, c1)
                         | uu____3739 -> failwith "Impossible")))
        | uu____3743 -> None
  
let norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3769 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____3769 with
        | None  -> None
        | Some (uu____3776,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____3781 = find1 l2  in
            (match uu____3781 with | None  -> Some l2 | Some l' -> Some l')
         in
      let res =
        let uu____3786 = FStar_Util.smap_try_find cache l.FStar_Ident.str  in
        match uu____3786 with
        | Some l1 -> l1
        | None  ->
            let uu____3789 = find1 l  in
            (match uu____3789 with
             | None  -> l
             | Some m -> (FStar_Util.smap_add cache l.FStar_Ident.str m; m))
         in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
  
let lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____3801 = lookup_qname env l1  in
      match uu____3801 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3813;
              FStar_Syntax_Syntax.sigrng = uu____3814;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3816;_},uu____3817),uu____3818)
          -> q
      | uu____3843 -> []
  
let lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3866 =
          let uu____3867 =
            let uu____3868 = FStar_Util.string_of_int i  in
            let uu____3869 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3868 uu____3869
             in
          failwith uu____3867  in
        let uu____3870 = lookup_datacon env lid  in
        match uu____3870 with
        | (uu____3873,t) ->
            let uu____3875 =
              let uu____3876 = FStar_Syntax_Subst.compress t  in
              uu____3876.FStar_Syntax_Syntax.n  in
            (match uu____3875 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3880) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____3901 =
                      FStar_Syntax_Util.mk_field_projector_name lid (fst b) i
                       in
                    FStar_All.pipe_right uu____3901 FStar_Pervasives.fst)
             | uu____3906 -> fail ())
  
let is_projector : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3913 = lookup_qname env l  in
      match uu____3913 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3924,uu____3925,uu____3926);
              FStar_Syntax_Syntax.sigrng = uu____3927;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3929;_},uu____3930),uu____3931)
          ->
          FStar_Util.for_some
            (fun uu___107_3956  ->
               match uu___107_3956 with
               | FStar_Syntax_Syntax.Projector uu____3957 -> true
               | uu____3960 -> false) quals
      | uu____3961 -> false
  
let is_datacon : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3978 = lookup_qname env lid  in
      match uu____3978 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3989,uu____3990,uu____3991,uu____3992,uu____3993,uu____3994);
              FStar_Syntax_Syntax.sigrng = uu____3995;
              FStar_Syntax_Syntax.sigquals = uu____3996;
              FStar_Syntax_Syntax.sigmeta = uu____3997;_},uu____3998),uu____3999)
          -> true
      | uu____4026 -> false
  
let is_record : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4043 = lookup_qname env lid  in
      match uu____4043 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4054,uu____4055,uu____4056,uu____4057,uu____4058,uu____4059);
              FStar_Syntax_Syntax.sigrng = uu____4060;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4062;_},uu____4063),uu____4064)
          ->
          FStar_Util.for_some
            (fun uu___108_4093  ->
               match uu___108_4093 with
               | FStar_Syntax_Syntax.RecordType uu____4094 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____4099 -> true
               | uu____4104 -> false) quals
      | uu____4105 -> false
  
let is_action : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4122 = lookup_qname env lid  in
      match uu____4122 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4133,uu____4134,uu____4135);
              FStar_Syntax_Syntax.sigrng = uu____4136;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4138;_},uu____4139),uu____4140)
          ->
          FStar_Util.for_some
            (fun uu___109_4169  ->
               match uu___109_4169 with
               | FStar_Syntax_Syntax.Action uu____4170 -> true
               | uu____4171 -> false) quals
      | uu____4172 -> false
  
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
      let uu____4191 =
        let uu____4192 = FStar_Syntax_Util.un_uinst head1  in
        uu____4192.FStar_Syntax_Syntax.n  in
      match uu____4191 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4196 -> false
  
let is_type_constructor : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match fst x with
        | FStar_Util.Inl uu____4234 -> Some false
        | FStar_Util.Inr (se,uu____4243) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4252 ->
                 Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4256 -> Some true
             | uu____4265 -> Some false)
         in
      let uu____4266 =
        let uu____4268 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____4268 mapper  in
      match uu____4266 with | Some b -> b | None  -> false
  
let num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4295 = lookup_qname env lid  in
      match uu____4295 with
      | Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4306,uu____4307,tps,uu____4309,uu____4310,uu____4311);
              FStar_Syntax_Syntax.sigrng = uu____4312;
              FStar_Syntax_Syntax.sigquals = uu____4313;
              FStar_Syntax_Syntax.sigmeta = uu____4314;_},uu____4315),uu____4316)
          -> FStar_List.length tps
      | uu____4348 ->
          let uu____4359 =
            let uu____4360 =
              let uu____4363 = name_not_found lid  in
              (uu____4363, (FStar_Ident.range_of_lid lid))  in
            FStar_Errors.Error uu____4360  in
          raise uu____4359
  
let effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4385  ->
              match uu____4385 with
              | (d,uu____4390) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4399 = effect_decl_opt env l  in
      match uu____4399 with
      | None  ->
          let uu____4407 =
            let uu____4408 =
              let uu____4411 = name_not_found l  in
              (uu____4411, (FStar_Ident.range_of_lid l))  in
            FStar_Errors.Error uu____4408  in
          raise uu____4407
      | Some md -> fst md
  
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
            (let uu____4454 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4478  ->
                       match uu____4478 with
                       | (m1,m2,uu____4486,uu____4487,uu____4488) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2)))
                in
             match uu____4454 with
             | None  ->
                 let uu____4497 =
                   let uu____4498 =
                     let uu____4501 =
                       let uu____4502 = FStar_Syntax_Print.lid_to_string l1
                          in
                       let uu____4503 = FStar_Syntax_Print.lid_to_string l2
                          in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4502
                         uu____4503
                        in
                     (uu____4501, (env.range))  in
                   FStar_Errors.Error uu____4498  in
                 raise uu____4497
             | Some (uu____4507,uu____4508,m3,j1,j2) -> (m3, j1, j2))
  
let monad_leq :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> edge option =
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
  let uu____4555 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4567  ->
            match uu____4567 with
            | (d,uu____4571) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
     in
  match uu____4555 with
  | None  ->
      let uu____4578 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str
         in
      failwith uu____4578
  | Some (md,_q) ->
      let uu____4587 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature))
         in
      (match uu____4587 with
       | (uu____4594,s) ->
           let s1 = FStar_Syntax_Subst.compress s  in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4602)::(wp,uu____4604)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4626 -> failwith "Impossible"))
  
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
                 let uu____4662 = get_range env  in
                 let uu____4663 =
                   let uu____4666 =
                     let uu____4667 =
                       let uu____4677 =
                         let uu____4679 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         [uu____4679]  in
                       (null_wp, uu____4677)  in
                     FStar_Syntax_Syntax.Tm_app uu____4667  in
                   FStar_Syntax_Syntax.mk uu____4666  in
                 uu____4663 None uu____4662  in
               let uu____4689 =
                 let uu____4690 =
                   let uu____4696 = FStar_Syntax_Syntax.as_arg null_wp_res
                      in
                   [uu____4696]  in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4690;
                   FStar_Syntax_Syntax.flags = []
                 }  in
               FStar_Syntax_Syntax.mk_Comp uu____4689)
  
let build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___120_4705 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___120_4705.order);
              joins = (uu___120_4705.joins)
            }  in
          let uu___121_4710 = env  in
          {
            solver = (uu___121_4710.solver);
            range = (uu___121_4710.range);
            curmodule = (uu___121_4710.curmodule);
            gamma = (uu___121_4710.gamma);
            gamma_cache = (uu___121_4710.gamma_cache);
            modules = (uu___121_4710.modules);
            expected_typ = (uu___121_4710.expected_typ);
            sigtab = (uu___121_4710.sigtab);
            is_pattern = (uu___121_4710.is_pattern);
            instantiate_imp = (uu___121_4710.instantiate_imp);
            effects;
            generalize = (uu___121_4710.generalize);
            letrecs = (uu___121_4710.letrecs);
            top_level = (uu___121_4710.top_level);
            check_uvars = (uu___121_4710.check_uvars);
            use_eq = (uu___121_4710.use_eq);
            is_iface = (uu___121_4710.is_iface);
            admit = (uu___121_4710.admit);
            lax = (uu___121_4710.lax);
            lax_universes = (uu___121_4710.lax_universes);
            type_of = (uu___121_4710.type_of);
            universe_of = (uu___121_4710.universe_of);
            use_bv_sorts = (uu___121_4710.use_bv_sorts);
            qname_and_index = (uu___121_4710.qname_and_index);
            proof_ns = (uu___121_4710.proof_ns);
            synth = (uu___121_4710.synth);
            is_native_tactic = (uu___121_4710.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4727 = (e1.mlift).mlift_wp r wp1  in
                (e2.mlift).mlift_wp r uu____4727  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (Some l1,Some l2) ->
                    Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4806 = (e1.mlift).mlift_wp t wp  in
                              let uu____4807 = l1 t wp e  in
                              l2 t uu____4806 uu____4807))
                | uu____4808 -> None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4843 = inst_tscheme lift_t  in
            match uu____4843 with
            | (uu____4848,lift_t1) ->
                let uu____4850 =
                  let uu____4853 =
                    let uu____4854 =
                      let uu____4864 =
                        let uu____4866 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4867 =
                          let uu____4869 = FStar_Syntax_Syntax.as_arg wp1  in
                          [uu____4869]  in
                        uu____4866 :: uu____4867  in
                      (lift_t1, uu____4864)  in
                    FStar_Syntax_Syntax.Tm_app uu____4854  in
                  FStar_Syntax_Syntax.mk uu____4853  in
                uu____4850 None wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
            | None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4914 = inst_tscheme lift_t  in
            match uu____4914 with
            | (uu____4919,lift_t1) ->
                let uu____4921 =
                  let uu____4924 =
                    let uu____4925 =
                      let uu____4935 =
                        let uu____4937 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____4938 =
                          let uu____4940 = FStar_Syntax_Syntax.as_arg wp1  in
                          let uu____4941 =
                            let uu____4943 = FStar_Syntax_Syntax.as_arg e  in
                            [uu____4943]  in
                          uu____4940 :: uu____4941  in
                        uu____4937 :: uu____4938  in
                      (lift_t1, uu____4935)  in
                    FStar_Syntax_Syntax.Tm_app uu____4925  in
                  FStar_Syntax_Syntax.mk uu____4924  in
                uu____4921 None e.FStar_Syntax_Syntax.pos
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
              let uu____4984 =
                let uu____4985 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____4985
                  FStar_Syntax_Syntax.Delta_constant None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____4984  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____4989 =
              let uu____4990 = l.mlift_wp arg wp  in
              FStar_Syntax_Print.term_to_string uu____4990  in
            let uu____4991 =
              let uu____4992 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____5007 = l1 arg wp e  in
                     FStar_Syntax_Print.term_to_string uu____5007)
                 in
              FStar_Util.dflt "none" uu____4992  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4989
              uu____4991
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____5020  ->
                    match uu____5020 with
                    | (e,uu____5025) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____5038 =
            match uu____5038 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i) (fun _0_39  -> Some _0_39)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____5063 =
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
                                    (let uu____5075 =
                                       let uu____5080 =
                                         find_edge order1 (i, k)  in
                                       let uu____5082 =
                                         find_edge order1 (k, j)  in
                                       (uu____5080, uu____5082)  in
                                     match uu____5075 with
                                     | (Some e1,Some e2) ->
                                         let uu____5091 = compose_edges e1 e2
                                            in
                                         [uu____5091]
                                     | uu____5092 -> [])))))
                 in
              FStar_List.append order1 uu____5063  in
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
                   let uu____5107 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Syntax_Const.effect_DIV_lid)
                       &&
                       (let uu____5108 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____5108
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____5107
                   then
                     let uu____5111 =
                       let uu____5112 =
                         let uu____5115 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         let uu____5116 = get_range env  in
                         (uu____5115, uu____5116)  in
                       FStar_Errors.Error uu____5112  in
                     raise uu____5111
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
                                            let uu____5179 =
                                              let uu____5184 =
                                                find_edge order2 (i, k)  in
                                              let uu____5186 =
                                                find_edge order2 (j, k)  in
                                              (uu____5184, uu____5186)  in
                                            match uu____5179 with
                                            | (Some ik,Some jk) ->
                                                (match bopt with
                                                 | None  -> Some (k, ik, jk)
                                                 | Some
                                                     (ub,uu____5209,uu____5210)
                                                     ->
                                                     let uu____5214 =
                                                       let uu____5217 =
                                                         let uu____5218 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____5218
                                                          in
                                                       let uu____5220 =
                                                         let uu____5221 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____5221
                                                          in
                                                       (uu____5217,
                                                         uu____5220)
                                                        in
                                                     (match uu____5214 with
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
                                            | uu____5240 -> bopt) None)
                                 in
                              match join_opt with
                              | None  -> []
                              | Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___122_5279 = env.effects  in
              { decls = (uu___122_5279.decls); order = order2; joins }  in
            let uu___123_5280 = env  in
            {
              solver = (uu___123_5280.solver);
              range = (uu___123_5280.range);
              curmodule = (uu___123_5280.curmodule);
              gamma = (uu___123_5280.gamma);
              gamma_cache = (uu___123_5280.gamma_cache);
              modules = (uu___123_5280.modules);
              expected_typ = (uu___123_5280.expected_typ);
              sigtab = (uu___123_5280.sigtab);
              is_pattern = (uu___123_5280.is_pattern);
              instantiate_imp = (uu___123_5280.instantiate_imp);
              effects;
              generalize = (uu___123_5280.generalize);
              letrecs = (uu___123_5280.letrecs);
              top_level = (uu___123_5280.top_level);
              check_uvars = (uu___123_5280.check_uvars);
              use_eq = (uu___123_5280.use_eq);
              is_iface = (uu___123_5280.is_iface);
              admit = (uu___123_5280.admit);
              lax = (uu___123_5280.lax);
              lax_universes = (uu___123_5280.lax_universes);
              type_of = (uu___123_5280.type_of);
              universe_of = (uu___123_5280.universe_of);
              use_bv_sorts = (uu___123_5280.use_bv_sorts);
              qname_and_index = (uu___123_5280.qname_and_index);
              proof_ns = (uu___123_5280.proof_ns);
              synth = (uu___123_5280.synth);
              is_native_tactic = (uu___123_5280.is_native_tactic)
            }))
      | uu____5281 -> env
  
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
        | uu____5303 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____5311 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____5311 with
      | None  -> c
      | Some (binders,cdef) ->
          let uu____5321 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____5321 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5338 =
                     let uu____5339 =
                       let uu____5342 =
                         let uu____5343 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1)
                            in
                         let uu____5349 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1"))
                            in
                         let uu____5357 =
                           let uu____5358 = FStar_Syntax_Syntax.mk_Comp c  in
                           FStar_Syntax_Print.comp_to_string uu____5358  in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5343 uu____5349 uu____5357
                          in
                       (uu____5342, (comp.FStar_Syntax_Syntax.pos))  in
                     FStar_Errors.Error uu____5339  in
                   raise uu____5338)
                else ();
                (let inst1 =
                   let uu____5362 =
                     let uu____5368 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____5368 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____5375  ->
                        fun uu____5376  ->
                          match (uu____5375, uu____5376) with
                          | ((x,uu____5390),(t,uu____5392)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5362
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____5407 =
                     let uu___124_5408 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___124_5408.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___124_5408.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___124_5408.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___124_5408.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____5407
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux only_reifiable env c u_c =
  let uu____5438 =
    let uu____5443 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)
       in
    effect_decl_opt env uu____5443  in
  match uu____5438 with
  | None  -> None
  | Some (ed,qualifiers) ->
      let uu____5459 =
        only_reifiable &&
          (let uu____5460 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
              in
           Prims.op_Negation uu____5460)
         in
      if uu____5459
      then None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> None
         | uu____5473 ->
             let c1 = unfold_effect_abbrev env c  in
             let uu____5475 =
               let uu____5484 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5484)  in
             (match uu____5475 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr))
                     in
                  let uu____5518 =
                    let uu____5521 = get_range env  in
                    let uu____5522 =
                      let uu____5525 =
                        let uu____5526 =
                          let uu____5536 =
                            let uu____5538 =
                              FStar_Syntax_Syntax.as_arg res_typ  in
                            [uu____5538; wp]  in
                          (repr, uu____5536)  in
                        FStar_Syntax_Syntax.Tm_app uu____5526  in
                      FStar_Syntax_Syntax.mk uu____5525  in
                    uu____5522 None uu____5521  in
                  Some uu____5518))
  
let effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax option
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
          let uu____5582 =
            let uu____5583 =
              let uu____5586 =
                let uu____5587 = FStar_Ident.string_of_lid l  in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5587
                 in
              let uu____5588 = get_range env  in (uu____5586, uu____5588)  in
            FStar_Errors.Error uu____5583  in
          raise uu____5582  in
        let uu____5589 = effect_repr_aux true env c u_c  in
        match uu____5589 with
        | None  -> no_reify (FStar_Syntax_Util.comp_effect_name c)
        | Some tm -> tm
  
let is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5621 -> false
  
let is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5628 =
        let uu____5629 = FStar_Syntax_Subst.compress t  in
        uu____5629.FStar_Syntax_Syntax.n  in
      match uu____5628 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5632,c) ->
          is_reifiable_comp env c
      | uu____5644 -> false
  
let push_in_gamma : env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5662)::uu____5663 -> x :: rest
        | (Binding_sig_inst uu____5668)::uu____5669 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5678 = push1 x rest1  in local :: uu____5678
         in
      let uu___125_5680 = env  in
      let uu____5681 = push1 s env.gamma  in
      {
        solver = (uu___125_5680.solver);
        range = (uu___125_5680.range);
        curmodule = (uu___125_5680.curmodule);
        gamma = uu____5681;
        gamma_cache = (uu___125_5680.gamma_cache);
        modules = (uu___125_5680.modules);
        expected_typ = (uu___125_5680.expected_typ);
        sigtab = (uu___125_5680.sigtab);
        is_pattern = (uu___125_5680.is_pattern);
        instantiate_imp = (uu___125_5680.instantiate_imp);
        effects = (uu___125_5680.effects);
        generalize = (uu___125_5680.generalize);
        letrecs = (uu___125_5680.letrecs);
        top_level = (uu___125_5680.top_level);
        check_uvars = (uu___125_5680.check_uvars);
        use_eq = (uu___125_5680.use_eq);
        is_iface = (uu___125_5680.is_iface);
        admit = (uu___125_5680.admit);
        lax = (uu___125_5680.lax);
        lax_universes = (uu___125_5680.lax_universes);
        type_of = (uu___125_5680.type_of);
        universe_of = (uu___125_5680.universe_of);
        use_bv_sorts = (uu___125_5680.use_bv_sorts);
        qname_and_index = (uu___125_5680.qname_and_index);
        proof_ns = (uu___125_5680.proof_ns);
        synth = (uu___125_5680.synth);
        is_native_tactic = (uu___125_5680.is_native_tactic)
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
      let uu___126_5708 = env  in
      {
        solver = (uu___126_5708.solver);
        range = (uu___126_5708.range);
        curmodule = (uu___126_5708.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___126_5708.gamma_cache);
        modules = (uu___126_5708.modules);
        expected_typ = (uu___126_5708.expected_typ);
        sigtab = (uu___126_5708.sigtab);
        is_pattern = (uu___126_5708.is_pattern);
        instantiate_imp = (uu___126_5708.instantiate_imp);
        effects = (uu___126_5708.effects);
        generalize = (uu___126_5708.generalize);
        letrecs = (uu___126_5708.letrecs);
        top_level = (uu___126_5708.top_level);
        check_uvars = (uu___126_5708.check_uvars);
        use_eq = (uu___126_5708.use_eq);
        is_iface = (uu___126_5708.is_iface);
        admit = (uu___126_5708.admit);
        lax = (uu___126_5708.lax);
        lax_universes = (uu___126_5708.lax_universes);
        type_of = (uu___126_5708.type_of);
        universe_of = (uu___126_5708.universe_of);
        use_bv_sorts = (uu___126_5708.use_bv_sorts);
        qname_and_index = (uu___126_5708.qname_and_index);
        proof_ns = (uu___126_5708.proof_ns);
        synth = (uu___126_5708.synth);
        is_native_tactic = (uu___126_5708.is_native_tactic)
      }
  
let push_bv : env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let pop_bv : env -> (FStar_Syntax_Syntax.bv * env) option =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        Some
          (x,
            (let uu___127_5729 = env  in
             {
               solver = (uu___127_5729.solver);
               range = (uu___127_5729.range);
               curmodule = (uu___127_5729.curmodule);
               gamma = rest;
               gamma_cache = (uu___127_5729.gamma_cache);
               modules = (uu___127_5729.modules);
               expected_typ = (uu___127_5729.expected_typ);
               sigtab = (uu___127_5729.sigtab);
               is_pattern = (uu___127_5729.is_pattern);
               instantiate_imp = (uu___127_5729.instantiate_imp);
               effects = (uu___127_5729.effects);
               generalize = (uu___127_5729.generalize);
               letrecs = (uu___127_5729.letrecs);
               top_level = (uu___127_5729.top_level);
               check_uvars = (uu___127_5729.check_uvars);
               use_eq = (uu___127_5729.use_eq);
               is_iface = (uu___127_5729.is_iface);
               admit = (uu___127_5729.admit);
               lax = (uu___127_5729.lax);
               lax_universes = (uu___127_5729.lax_universes);
               type_of = (uu___127_5729.type_of);
               universe_of = (uu___127_5729.universe_of);
               use_bv_sorts = (uu___127_5729.use_bv_sorts);
               qname_and_index = (uu___127_5729.qname_and_index);
               proof_ns = (uu___127_5729.proof_ns);
               synth = (uu___127_5729.synth);
               is_native_tactic = (uu___127_5729.is_native_tactic)
             }))
    | uu____5730 -> None
  
let push_binders : env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5743  ->
             match uu____5743 with | (x,uu____5747) -> push_bv env1 x) env bs
  
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
            let uu___128_5767 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___128_5767.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___128_5767.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (snd t)
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
      (let uu___129_5797 = env  in
       {
         solver = (uu___129_5797.solver);
         range = (uu___129_5797.range);
         curmodule = (uu___129_5797.curmodule);
         gamma = [];
         gamma_cache = (uu___129_5797.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = None;
         sigtab = (uu___129_5797.sigtab);
         is_pattern = (uu___129_5797.is_pattern);
         instantiate_imp = (uu___129_5797.instantiate_imp);
         effects = (uu___129_5797.effects);
         generalize = (uu___129_5797.generalize);
         letrecs = (uu___129_5797.letrecs);
         top_level = (uu___129_5797.top_level);
         check_uvars = (uu___129_5797.check_uvars);
         use_eq = (uu___129_5797.use_eq);
         is_iface = (uu___129_5797.is_iface);
         admit = (uu___129_5797.admit);
         lax = (uu___129_5797.lax);
         lax_universes = (uu___129_5797.lax_universes);
         type_of = (uu___129_5797.type_of);
         universe_of = (uu___129_5797.universe_of);
         use_bv_sorts = (uu___129_5797.use_bv_sorts);
         qname_and_index = (uu___129_5797.qname_and_index);
         proof_ns = (uu___129_5797.proof_ns);
         synth = (uu___129_5797.synth);
         is_native_tactic = (uu___129_5797.is_native_tactic)
       })
  
let push_univ_vars : env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
let open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____5821 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____5821 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____5837 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____5837)
  
let set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___130_5847 = env  in
      {
        solver = (uu___130_5847.solver);
        range = (uu___130_5847.range);
        curmodule = (uu___130_5847.curmodule);
        gamma = (uu___130_5847.gamma);
        gamma_cache = (uu___130_5847.gamma_cache);
        modules = (uu___130_5847.modules);
        expected_typ = (Some t);
        sigtab = (uu___130_5847.sigtab);
        is_pattern = (uu___130_5847.is_pattern);
        instantiate_imp = (uu___130_5847.instantiate_imp);
        effects = (uu___130_5847.effects);
        generalize = (uu___130_5847.generalize);
        letrecs = (uu___130_5847.letrecs);
        top_level = (uu___130_5847.top_level);
        check_uvars = (uu___130_5847.check_uvars);
        use_eq = false;
        is_iface = (uu___130_5847.is_iface);
        admit = (uu___130_5847.admit);
        lax = (uu___130_5847.lax);
        lax_universes = (uu___130_5847.lax_universes);
        type_of = (uu___130_5847.type_of);
        universe_of = (uu___130_5847.universe_of);
        use_bv_sorts = (uu___130_5847.use_bv_sorts);
        qname_and_index = (uu___130_5847.qname_and_index);
        proof_ns = (uu___130_5847.proof_ns);
        synth = (uu___130_5847.synth);
        is_native_tactic = (uu___130_5847.is_native_tactic)
      }
  
let expected_typ : env -> FStar_Syntax_Syntax.typ option =
  fun env  -> match env.expected_typ with | None  -> None | Some t -> Some t 
let clear_expected_typ : env -> (env * FStar_Syntax_Syntax.typ option) =
  fun env_  ->
    let uu____5863 = expected_typ env_  in
    ((let uu___131_5866 = env_  in
      {
        solver = (uu___131_5866.solver);
        range = (uu___131_5866.range);
        curmodule = (uu___131_5866.curmodule);
        gamma = (uu___131_5866.gamma);
        gamma_cache = (uu___131_5866.gamma_cache);
        modules = (uu___131_5866.modules);
        expected_typ = None;
        sigtab = (uu___131_5866.sigtab);
        is_pattern = (uu___131_5866.is_pattern);
        instantiate_imp = (uu___131_5866.instantiate_imp);
        effects = (uu___131_5866.effects);
        generalize = (uu___131_5866.generalize);
        letrecs = (uu___131_5866.letrecs);
        top_level = (uu___131_5866.top_level);
        check_uvars = (uu___131_5866.check_uvars);
        use_eq = false;
        is_iface = (uu___131_5866.is_iface);
        admit = (uu___131_5866.admit);
        lax = (uu___131_5866.lax);
        lax_universes = (uu___131_5866.lax_universes);
        type_of = (uu___131_5866.type_of);
        universe_of = (uu___131_5866.universe_of);
        use_bv_sorts = (uu___131_5866.use_bv_sorts);
        qname_and_index = (uu___131_5866.qname_and_index);
        proof_ns = (uu___131_5866.proof_ns);
        synth = (uu___131_5866.synth);
        is_native_tactic = (uu___131_5866.is_native_tactic)
      }), uu____5863)
  
let finish_module : env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""]  in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Syntax_Const.prims_lid
        then
          let uu____5877 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___110_5881  ->
                    match uu___110_5881 with
                    | Binding_sig (uu____5883,se) -> [se]
                    | uu____5887 -> []))
             in
          FStar_All.pipe_right uu____5877 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___132_5892 = env  in
       {
         solver = (uu___132_5892.solver);
         range = (uu___132_5892.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___132_5892.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___132_5892.expected_typ);
         sigtab = (uu___132_5892.sigtab);
         is_pattern = (uu___132_5892.is_pattern);
         instantiate_imp = (uu___132_5892.instantiate_imp);
         effects = (uu___132_5892.effects);
         generalize = (uu___132_5892.generalize);
         letrecs = (uu___132_5892.letrecs);
         top_level = (uu___132_5892.top_level);
         check_uvars = (uu___132_5892.check_uvars);
         use_eq = (uu___132_5892.use_eq);
         is_iface = (uu___132_5892.is_iface);
         admit = (uu___132_5892.admit);
         lax = (uu___132_5892.lax);
         lax_universes = (uu___132_5892.lax_universes);
         type_of = (uu___132_5892.type_of);
         universe_of = (uu___132_5892.universe_of);
         use_bv_sorts = (uu___132_5892.use_bv_sorts);
         qname_and_index = (uu___132_5892.qname_and_index);
         proof_ns = (uu___132_5892.proof_ns);
         synth = (uu___132_5892.synth);
         is_native_tactic = (uu___132_5892.is_native_tactic)
       })
  
let uvars_in_env :
  env -> (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set
  =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5942)::tl1 -> aux out tl1
      | (Binding_lid (uu____5945,(uu____5946,t)))::tl1 ->
          let uu____5955 =
            let uu____5959 = FStar_Syntax_Free.uvars t  in ext out uu____5959
             in
          aux uu____5955 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5963;
            FStar_Syntax_Syntax.index = uu____5964;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5970 =
            let uu____5974 = FStar_Syntax_Free.uvars t  in ext out uu____5974
             in
          aux uu____5970 tl1
      | (Binding_sig uu____5978)::uu____5979 -> out
      | (Binding_sig_inst uu____5984)::uu____5985 -> out  in
    aux no_uvs env.gamma
  
let univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6022)::tl1 -> aux out tl1
      | (Binding_univ uu____6029)::tl1 -> aux out tl1
      | (Binding_lid (uu____6032,(uu____6033,t)))::tl1 ->
          let uu____6042 =
            let uu____6044 = FStar_Syntax_Free.univs t  in ext out uu____6044
             in
          aux uu____6042 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6046;
            FStar_Syntax_Syntax.index = uu____6047;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6053 =
            let uu____6055 = FStar_Syntax_Free.univs t  in ext out uu____6055
             in
          aux uu____6053 tl1
      | (Binding_sig uu____6057)::uu____6058 -> out  in
    aux no_univs env.gamma
  
let univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____6095)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____6105 = FStar_Util.set_add uname out  in
          aux uu____6105 tl1
      | (Binding_lid (uu____6107,(uu____6108,t)))::tl1 ->
          let uu____6117 =
            let uu____6119 = FStar_Syntax_Free.univnames t  in
            ext out uu____6119  in
          aux uu____6117 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6121;
            FStar_Syntax_Syntax.index = uu____6122;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6128 =
            let uu____6130 = FStar_Syntax_Free.univnames t  in
            ext out uu____6130  in
          aux uu____6128 tl1
      | (Binding_sig uu____6132)::uu____6133 -> out  in
    aux no_univ_names env.gamma
  
let bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___111_6149  ->
            match uu___111_6149 with
            | Binding_var x -> [x]
            | Binding_lid uu____6152 -> []
            | Binding_sig uu____6155 -> []
            | Binding_univ uu____6159 -> []
            | Binding_sig_inst uu____6160 -> []))
  
let binders_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6170 =
      let uu____6172 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____6172
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____6170 FStar_List.rev
  
let bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma 
let all_binders : env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma 
let print_gamma : env -> Prims.unit =
  fun env  ->
    let uu____6188 =
      let uu____6189 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___112_6193  ->
                match uu___112_6193 with
                | Binding_var x ->
                    let uu____6195 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____6195
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6198) ->
                    let uu____6199 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____6199
                | Binding_sig (ls,uu____6201) ->
                    let uu____6204 =
                      let uu____6205 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____6205
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____6204
                | Binding_sig_inst (ls,uu____6211,uu____6212) ->
                    let uu____6215 =
                      let uu____6216 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____6216
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____6215))
         in
      FStar_All.pipe_right uu____6189 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____6188 (FStar_Util.print1 "%s\n")
  
let eq_gamma : env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6228 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____6228
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6245  ->
                 fun uu____6246  ->
                   match (uu____6245, uu____6246) with
                   | ((b1,uu____6256),(b2,uu____6258)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a 
let lidents : env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___113_6301  ->
             match uu___113_6301 with
             | Binding_sig (lids,uu____6305) -> FStar_List.append lids keys
             | uu____6308 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6310  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let should_enc_path : env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____6335) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____6347,uu____6348) -> false  in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____6372 = list_prefix p path1  in
            if uu____6372 then b else should_enc_path' pns1 path1
         in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
  
let should_enc_lid : env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6382 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____6382
  
let cons_proof_ns : Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns  in
            let uu___133_6402 = e  in
            {
              solver = (uu___133_6402.solver);
              range = (uu___133_6402.range);
              curmodule = (uu___133_6402.curmodule);
              gamma = (uu___133_6402.gamma);
              gamma_cache = (uu___133_6402.gamma_cache);
              modules = (uu___133_6402.modules);
              expected_typ = (uu___133_6402.expected_typ);
              sigtab = (uu___133_6402.sigtab);
              is_pattern = (uu___133_6402.is_pattern);
              instantiate_imp = (uu___133_6402.instantiate_imp);
              effects = (uu___133_6402.effects);
              generalize = (uu___133_6402.generalize);
              letrecs = (uu___133_6402.letrecs);
              top_level = (uu___133_6402.top_level);
              check_uvars = (uu___133_6402.check_uvars);
              use_eq = (uu___133_6402.use_eq);
              is_iface = (uu___133_6402.is_iface);
              admit = (uu___133_6402.admit);
              lax = (uu___133_6402.lax);
              lax_universes = (uu___133_6402.lax_universes);
              type_of = (uu___133_6402.type_of);
              universe_of = (uu___133_6402.universe_of);
              use_bv_sorts = (uu___133_6402.use_bv_sorts);
              qname_and_index = (uu___133_6402.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___133_6402.synth);
              is_native_tactic = (uu___133_6402.is_native_tactic)
            }
  
let add_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path 
let rem_proof_ns : env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path 
let push_proof_ns : env -> env =
  fun e  ->
    let uu___134_6421 = e  in
    {
      solver = (uu___134_6421.solver);
      range = (uu___134_6421.range);
      curmodule = (uu___134_6421.curmodule);
      gamma = (uu___134_6421.gamma);
      gamma_cache = (uu___134_6421.gamma_cache);
      modules = (uu___134_6421.modules);
      expected_typ = (uu___134_6421.expected_typ);
      sigtab = (uu___134_6421.sigtab);
      is_pattern = (uu___134_6421.is_pattern);
      instantiate_imp = (uu___134_6421.instantiate_imp);
      effects = (uu___134_6421.effects);
      generalize = (uu___134_6421.generalize);
      letrecs = (uu___134_6421.letrecs);
      top_level = (uu___134_6421.top_level);
      check_uvars = (uu___134_6421.check_uvars);
      use_eq = (uu___134_6421.use_eq);
      is_iface = (uu___134_6421.is_iface);
      admit = (uu___134_6421.admit);
      lax = (uu___134_6421.lax);
      lax_universes = (uu___134_6421.lax_universes);
      type_of = (uu___134_6421.type_of);
      universe_of = (uu___134_6421.universe_of);
      use_bv_sorts = (uu___134_6421.use_bv_sorts);
      qname_and_index = (uu___134_6421.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___134_6421.synth);
      is_native_tactic = (uu___134_6421.is_native_tactic)
    }
  
let pop_proof_ns : env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____6430::rest ->
        let uu___135_6433 = e  in
        {
          solver = (uu___135_6433.solver);
          range = (uu___135_6433.range);
          curmodule = (uu___135_6433.curmodule);
          gamma = (uu___135_6433.gamma);
          gamma_cache = (uu___135_6433.gamma_cache);
          modules = (uu___135_6433.modules);
          expected_typ = (uu___135_6433.expected_typ);
          sigtab = (uu___135_6433.sigtab);
          is_pattern = (uu___135_6433.is_pattern);
          instantiate_imp = (uu___135_6433.instantiate_imp);
          effects = (uu___135_6433.effects);
          generalize = (uu___135_6433.generalize);
          letrecs = (uu___135_6433.letrecs);
          top_level = (uu___135_6433.top_level);
          check_uvars = (uu___135_6433.check_uvars);
          use_eq = (uu___135_6433.use_eq);
          is_iface = (uu___135_6433.is_iface);
          admit = (uu___135_6433.admit);
          lax = (uu___135_6433.lax);
          lax_universes = (uu___135_6433.lax_universes);
          type_of = (uu___135_6433.type_of);
          universe_of = (uu___135_6433.universe_of);
          use_bv_sorts = (uu___135_6433.use_bv_sorts);
          qname_and_index = (uu___135_6433.qname_and_index);
          proof_ns = rest;
          synth = (uu___135_6433.synth);
          is_native_tactic = (uu___135_6433.is_native_tactic)
        }
  
let get_proof_ns : env -> proof_namespace = fun e  -> e.proof_ns 
let set_proof_ns : proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___136_6443 = e  in
      {
        solver = (uu___136_6443.solver);
        range = (uu___136_6443.range);
        curmodule = (uu___136_6443.curmodule);
        gamma = (uu___136_6443.gamma);
        gamma_cache = (uu___136_6443.gamma_cache);
        modules = (uu___136_6443.modules);
        expected_typ = (uu___136_6443.expected_typ);
        sigtab = (uu___136_6443.sigtab);
        is_pattern = (uu___136_6443.is_pattern);
        instantiate_imp = (uu___136_6443.instantiate_imp);
        effects = (uu___136_6443.effects);
        generalize = (uu___136_6443.generalize);
        letrecs = (uu___136_6443.letrecs);
        top_level = (uu___136_6443.top_level);
        check_uvars = (uu___136_6443.check_uvars);
        use_eq = (uu___136_6443.use_eq);
        is_iface = (uu___136_6443.is_iface);
        admit = (uu___136_6443.admit);
        lax = (uu___136_6443.lax);
        lax_universes = (uu___136_6443.lax_universes);
        type_of = (uu___136_6443.type_of);
        universe_of = (uu___136_6443.universe_of);
        use_bv_sorts = (uu___136_6443.use_bv_sorts);
        qname_and_index = (uu___136_6443.qname_and_index);
        proof_ns = ns;
        synth = (uu___136_6443.synth);
        is_native_tactic = (uu___136_6443.is_native_tactic)
      }
  
let string_of_proof_ns : env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____6461 =
        FStar_List.map
          (fun fpns  ->
             let uu____6472 =
               let uu____6473 =
                 let uu____6474 =
                   FStar_List.map
                     (fun uu____6479  ->
                        match uu____6479 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns
                    in
                 FStar_String.concat "," uu____6474  in
               Prims.strcat uu____6473 "]"  in
             Prims.strcat "[" uu____6472) pns
         in
      FStar_String.concat ";" uu____6461  in
    string_of_proof_ns' env.proof_ns
  
let dummy_solver : solver_t =
  {
    init = (fun uu____6488  -> ());
    push = (fun uu____6489  -> ());
    pop = (fun uu____6490  -> ());
    mark = (fun uu____6491  -> ());
    reset_mark = (fun uu____6492  -> ());
    commit_mark = (fun uu____6493  -> ());
    encode_modul = (fun uu____6494  -> fun uu____6495  -> ());
    encode_sig = (fun uu____6496  -> fun uu____6497  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____6500 =
             let uu____6504 = FStar_Options.peek ()  in (e, g, uu____6504)
              in
           [uu____6500]);
    solve = (fun uu____6511  -> fun uu____6512  -> fun uu____6513  -> ());
    is_trivial = (fun uu____6517  -> fun uu____6518  -> false);
    finish = (fun uu____6519  -> ());
    refresh = (fun uu____6520  -> ())
  } 