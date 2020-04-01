open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____58 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____93 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  wl_deferred_to_tac:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred_to_tac
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_implicits
  
let (as_deferred :
  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def  ->
    FStar_List.map
      (fun uu____692  ->
         match uu____692 with
         | (uu____708,m,p) ->
             let uu____719 = FStar_Thunk.force m  in (uu____719, p)) wl_def
  
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl  ->
    fun d  ->
      FStar_List.map
        (fun uu____771  ->
           match uu____771 with
           | (m,p) ->
               let uu____791 = FStar_Thunk.mkv m  in ((wl.ctr), uu____791, p))
        d
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                FStar_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
                  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
                    worklist))
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                fun meta  ->
                  let ctx_uvar =
                    let uu____884 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____884;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    }  in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                       FStar_Pervasives_Native.None r
                      in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (let uu____916 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____916
                    then
                      let uu____920 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____920
                    else ());
                   (ctx_uvar, t,
                     ((let uu___86_926 = wl  in
                       {
                         attempting = (uu___86_926.attempting);
                         wl_deferred = (uu___86_926.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___86_926.wl_deferred_to_tac);
                         ctr = (uu___86_926.ctr);
                         defer_ok = (uu___86_926.defer_ok);
                         smt_ok = (uu___86_926.smt_ok);
                         umax_heuristic_ok = (uu___86_926.umax_heuristic_ok);
                         tcenv = (uu___86_926.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits))
                       }))))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
            worklist))
  =
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___92_959 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___92_959.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___92_959.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___92_959.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___92_959.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___92_959.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___92_959.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___92_959.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___92_959.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___92_959.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___92_959.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___92_959.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___92_959.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___92_959.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___92_959.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___92_959.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___92_959.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___92_959.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___92_959.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___92_959.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___92_959.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___92_959.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___92_959.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___92_959.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___92_959.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___92_959.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___92_959.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___92_959.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___92_959.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___92_959.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___92_959.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___92_959.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___92_959.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___92_959.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___92_959.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___92_959.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___92_959.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___92_959.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___92_959.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___92_959.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___92_959.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___92_959.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___92_959.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___92_959.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___92_959.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___92_959.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___92_959.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___92_959.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____961 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____961 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1052 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1093 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
let (extend_wl :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      FStar_TypeChecker_Common.implicits -> worklist)
  =
  fun wl  ->
    fun defer_to_tac  ->
      fun imps  ->
        let uu___101_1130 = wl  in
        let uu____1131 =
          let uu____1141 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1141  in
        {
          attempting = (uu___101_1130.attempting);
          wl_deferred = (uu___101_1130.wl_deferred);
          wl_deferred_to_tac = uu____1131;
          ctr = (uu___101_1130.ctr);
          defer_ok = (uu___101_1130.defer_ok);
          smt_ok = (uu___101_1130.smt_ok);
          umax_heuristic_ok = (uu___101_1130.umax_heuristic_ok);
          tcenv = (uu___101_1130.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps)
        }
  
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1167 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1178 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1189 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1207  ->
    match uu___0_1207 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1219 = FStar_Syntax_Util.head_and_args t  in
    match uu____1219 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1282 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1284 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1299 =
                     let uu____1301 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1301  in
                   FStar_Util.format1 "@<%s>" uu____1299
                in
             let uu____1305 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1282 uu____1284 uu____1305
         | uu____1308 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1320  ->
      match uu___1_1320 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1325 =
            let uu____1329 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1331 =
              let uu____1335 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1337 =
                let uu____1341 =
                  let uu____1345 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1345]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1341
                 in
              uu____1335 :: uu____1337  in
            uu____1329 :: uu____1331  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1325
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1356 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1358 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1360 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1356 uu____1358
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1360
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1374  ->
      match uu___2_1374 with
      | UNIV (u,t) ->
          let x =
            let uu____1380 = FStar_Options.hide_uvar_nums ()  in
            if uu____1380
            then "?"
            else
              (let uu____1387 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1387 FStar_Util.string_of_int)
             in
          let uu____1391 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1391
      | TERM (u,t) ->
          let x =
            let uu____1398 = FStar_Options.hide_uvar_nums ()  in
            if uu____1398
            then "?"
            else
              (let uu____1405 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1405 FStar_Util.string_of_int)
             in
          let uu____1409 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1409
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1428 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1428 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1449 =
      let uu____1453 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1453
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1449 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1472 .
    (FStar_Syntax_Syntax.term * 'Auu____1472) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1491 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1512  ->
              match uu____1512 with
              | (x,uu____1519) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1491 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
      wl_deferred_to_tac = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1566 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1566
         then
           let uu____1571 = FStar_Thunk.force reason  in
           let uu____1574 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1571 uu____1574
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1597 = FStar_Thunk.mk (fun uu____1600  -> reason)  in
        giveup env uu____1597 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1606  ->
    match uu___3_1606 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1612 .
    'Auu____1612 FStar_TypeChecker_Common.problem ->
      'Auu____1612 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___161_1624 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___161_1624.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___161_1624.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___161_1624.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___161_1624.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___161_1624.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___161_1624.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___161_1624.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1632 .
    'Auu____1632 FStar_TypeChecker_Common.problem ->
      'Auu____1632 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1652  ->
    match uu___4_1652 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1658  -> FStar_TypeChecker_Common.TProb _1658)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1664  -> FStar_TypeChecker_Common.CProb _1664)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1670  ->
    match uu___5_1670 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___173_1676 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___173_1676.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___173_1676.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___173_1676.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___173_1676.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___173_1676.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___173_1676.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___173_1676.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___173_1676.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___173_1676.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___177_1684 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___177_1684.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___177_1684.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___177_1684.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___177_1684.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___177_1684.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___177_1684.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___177_1684.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___177_1684.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___177_1684.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1697  ->
      match uu___6_1697 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1704  ->
    match uu___7_1704 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1717  ->
    match uu___8_1717 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1732  ->
    match uu___9_1732 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1747  ->
    match uu___10_1747 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1761  ->
    match uu___11_1761 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1775  ->
    match uu___12_1775 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1787  ->
    match uu___13_1787 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1803 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1803) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1833 =
          let uu____1835 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1835  in
        if uu____1833
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1872)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1919 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1943 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1943]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1919
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1971 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1995 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1995]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1971
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____2042 =
          let uu____2044 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2044  in
        if uu____2042
        then ()
        else
          (let uu____2049 =
             let uu____2052 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2052
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2049 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____2101 =
          let uu____2103 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2103  in
        if uu____2101
        then ()
        else
          (let uu____2108 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____2108)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____2128 =
        let uu____2130 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____2130  in
      if uu____2128
      then ()
      else
        (let msgf m =
           let uu____2144 =
             let uu____2146 =
               let uu____2148 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____2148 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____2146  in
           Prims.op_Hat msg uu____2144  in
         (let uu____2153 = msgf "scope"  in
          let uu____2156 = p_scope prob  in
          def_scope_wf uu____2153 (p_loc prob) uu____2156);
         (let uu____2168 = msgf "guard"  in
          def_check_scoped uu____2168 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2175 = msgf "lhs"  in
                def_check_scoped uu____2175 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2178 = msgf "rhs"  in
                def_check_scoped uu____2178 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2185 = msgf "lhs"  in
                def_check_scoped_comp uu____2185 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2188 = msgf "rhs"  in
                def_check_scoped_comp uu____2188 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___270_2209 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___270_2209.wl_deferred);
          wl_deferred_to_tac = (uu___270_2209.wl_deferred_to_tac);
          ctr = (uu___270_2209.ctr);
          defer_ok = (uu___270_2209.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___270_2209.umax_heuristic_ok);
          tcenv = (uu___270_2209.tcenv);
          wl_implicits = (uu___270_2209.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____2217 .
    FStar_TypeChecker_Env.env ->
      ('Auu____2217 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___274_2240 = empty_worklist env  in
      let uu____2241 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____2241;
        wl_deferred = (uu___274_2240.wl_deferred);
        wl_deferred_to_tac = (uu___274_2240.wl_deferred_to_tac);
        ctr = (uu___274_2240.ctr);
        defer_ok = (uu___274_2240.defer_ok);
        smt_ok = (uu___274_2240.smt_ok);
        umax_heuristic_ok = (uu___274_2240.umax_heuristic_ok);
        tcenv = (uu___274_2240.tcenv);
        wl_implicits = (uu___274_2240.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___279_2262 = wl  in
        {
          attempting = (uu___279_2262.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___279_2262.wl_deferred_to_tac);
          ctr = (uu___279_2262.ctr);
          defer_ok = (uu___279_2262.defer_ok);
          smt_ok = (uu___279_2262.smt_ok);
          umax_heuristic_ok = (uu___279_2262.umax_heuristic_ok);
          tcenv = (uu___279_2262.tcenv);
          wl_implicits = (uu___279_2262.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____2289 = FStar_Thunk.mkv reason  in defer uu____2289 prob wl
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (match u.FStar_Syntax_Syntax.ctx_uvar_meta with
         | FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Ctx_uvar_meta_attr a) ->
             let hooks =
               FStar_TypeChecker_Env.lookup_attr env
                 FStar_Parser_Const.resolve_implicits_attr_string
                in
             let should_defer =
               FStar_All.pipe_right hooks
                 (FStar_Util.for_some
                    (fun hook  ->
                       FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                         (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
                in
             should_defer
         | uu____2325 -> false)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___297_2346 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___297_2346.wl_deferred);
         wl_deferred_to_tac = (uu___297_2346.wl_deferred_to_tac);
         ctr = (uu___297_2346.ctr);
         defer_ok = (uu___297_2346.defer_ok);
         smt_ok = (uu___297_2346.smt_ok);
         umax_heuristic_ok = (uu___297_2346.umax_heuristic_ok);
         tcenv = (uu___297_2346.tcenv);
         wl_implicits = (uu___297_2346.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2360 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2360 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2394 = FStar_Syntax_Util.type_u ()  in
            match uu____2394 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2406 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2406 with
                 | (uu____2418,tt,wl1) ->
                     let uu____2421 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2421, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2427  ->
    match uu___14_2427 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2433  -> FStar_TypeChecker_Common.TProb _2433) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2439  -> FStar_TypeChecker_Common.CProb _2439) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2447 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2447 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2467  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2509 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2509 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2509 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2509 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2596 =
                          let uu____2605 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2605]  in
                        FStar_List.append scope uu____2596
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2648 =
                      let uu____2651 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2651  in
                    FStar_List.append uu____2648
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2670 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2670 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2690 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2690;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu____2764 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2764 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu____2852 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2852 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2890 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2890 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2890 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2890 FStar_TypeChecker_Common.problem *
                      worklist)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2958 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2958]  in
                        let uu____2977 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2977
                     in
                  let uu____2980 =
                    let uu____2987 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___380_2998 = wl  in
                       {
                         attempting = (uu___380_2998.attempting);
                         wl_deferred = (uu___380_2998.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___380_2998.wl_deferred_to_tac);
                         ctr = (uu___380_2998.ctr);
                         defer_ok = (uu___380_2998.defer_ok);
                         smt_ok = (uu___380_2998.smt_ok);
                         umax_heuristic_ok =
                           (uu___380_2998.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___380_2998.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2987
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2980 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3010 =
                              let uu____3015 =
                                let uu____3016 =
                                  let uu____3025 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3025
                                   in
                                [uu____3016]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3015  in
                            uu____3010 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3053 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3053;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (prob, wl1)
  
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____3101 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3101;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'Auu____3116 .
    worklist ->
      'Auu____3116 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____3149 =
                let uu____3152 =
                  let uu____3153 =
                    let uu____3160 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3160)  in
                  FStar_Syntax_Syntax.NT uu____3153  in
                [uu____3152]  in
              FStar_Syntax_Subst.subst uu____3149 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3182 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3182
        then
          let uu____3190 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3193 = prob_to_string env d  in
          let uu____3195 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3202 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3190 uu____3193 uu____3195 uu____3202
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3214 -> failwith "impossible"  in
           let uu____3217 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.term_to_string env)
                   tp.FStar_TypeChecker_Common.lhs
                   tp.FStar_TypeChecker_Common.rhs
             | FStar_TypeChecker_Common.CProb cp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.comp_to_string env)
                   cp.FStar_TypeChecker_Common.lhs
                   cp.FStar_TypeChecker_Common.rhs
              in
           match uu____3217 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3260  ->
            match uu___15_3260 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3272 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3276 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3276 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3307  ->
           match uu___16_3307 with
           | UNIV uu____3310 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3317 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3317
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___17_3345  ->
           match uu___17_3345 with
           | UNIV (u',t) ->
               let uu____3350 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3350
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3357 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3369 =
        let uu____3370 =
          let uu____3371 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3371
           in
        FStar_Syntax_Subst.compress uu____3370  in
      FStar_All.pipe_right uu____3369 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3383 =
        let uu____3384 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3384  in
      FStar_All.pipe_right uu____3383 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3396 =
        let uu____3400 =
          let uu____3402 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3402  in
        FStar_Pervasives_Native.Some uu____3400  in
      FStar_Profiling.profile (fun uu____3405  -> sn' env t) uu____3396
        "FStar.TypeChecker.Rel.sn"
  
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag  ->
    fun steps  ->
      fun env  ->
        fun t  ->
          let uu____3430 =
            let uu____3434 =
              let uu____3436 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3436  in
            FStar_Pervasives_Native.Some uu____3434  in
          FStar_Profiling.profile
            (fun uu____3439  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3430
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3447 = FStar_Syntax_Util.head_and_args t  in
    match uu____3447 with
    | (h,uu____3466) ->
        let uu____3491 =
          let uu____3492 = FStar_Syntax_Subst.compress h  in
          uu____3492.FStar_Syntax_Syntax.n  in
        (match uu____3491 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3497 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3510 =
        let uu____3514 =
          let uu____3516 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3516  in
        FStar_Pervasives_Native.Some uu____3514  in
      FStar_Profiling.profile
        (fun uu____3521  ->
           let uu____3522 = should_strongly_reduce t  in
           if uu____3522
           then
             let uu____3525 =
               let uu____3526 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3526  in
             FStar_All.pipe_right uu____3525 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3510 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3537 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3537) ->
        (FStar_Syntax_Syntax.term * 'Auu____3537)
  =
  fun env  ->
    fun t  ->
      let uu____3560 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3560, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____3612  ->
              match uu____3612 with
              | (x,imp) ->
                  let uu____3631 =
                    let uu___486_3632 = x  in
                    let uu____3633 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___486_3632.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___486_3632.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3633
                    }  in
                  (uu____3631, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3657 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3657
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3661 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3661
        | uu____3664 -> u2  in
      let uu____3665 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3665
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3682 =
          let uu____3686 =
            let uu____3688 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3688  in
          FStar_Pervasives_Native.Some uu____3686  in
        FStar_Profiling.profile
          (fun uu____3691  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3682 "FStar.TypeChecker.Rel.normalize_refinement"
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3813 = norm_refinement env t12  in
                 match uu____3813 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3828;
                     FStar_Syntax_Syntax.vars = uu____3829;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3853 =
                       let uu____3855 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3857 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3855 uu____3857
                        in
                     failwith uu____3853)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3873 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3873
          | FStar_Syntax_Syntax.Tm_uinst uu____3874 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3911 =
                   let uu____3912 = FStar_Syntax_Subst.compress t1'  in
                   uu____3912.FStar_Syntax_Syntax.n  in
                 match uu____3911 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3927 -> aux true t1'
                 | uu____3935 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3950 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3981 =
                   let uu____3982 = FStar_Syntax_Subst.compress t1'  in
                   uu____3982.FStar_Syntax_Syntax.n  in
                 match uu____3981 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3997 -> aux true t1'
                 | uu____4005 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4020 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4067 =
                   let uu____4068 = FStar_Syntax_Subst.compress t1'  in
                   uu____4068.FStar_Syntax_Syntax.n  in
                 match uu____4067 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4083 -> aux true t1'
                 | uu____4091 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4106 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4121 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4136 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4151 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4166 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4195 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4228 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4249 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4276 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4304 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4341 ->
              let uu____4348 =
                let uu____4350 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4352 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4350 uu____4352
                 in
              failwith uu____4348
          | FStar_Syntax_Syntax.Tm_ascribed uu____4367 ->
              let uu____4394 =
                let uu____4396 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4398 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4396 uu____4398
                 in
              failwith uu____4394
          | FStar_Syntax_Syntax.Tm_delayed uu____4413 ->
              let uu____4428 =
                let uu____4430 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4432 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4430 uu____4432
                 in
              failwith uu____4428
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4447 =
                let uu____4449 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4451 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4449 uu____4451
                 in
              failwith uu____4447
           in
        let uu____4466 = whnf env t1  in aux false uu____4466
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____4511 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4511 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4552 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4552, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4579 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4579 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4639  ->
    match uu____4639 with
    | (t_base,refopt) ->
        let uu____4670 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4670 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4712 =
      let uu____4716 =
        let uu____4719 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4744  ->
                  match uu____4744 with | (uu____4752,uu____4753,x) -> x))
           in
        FStar_List.append wl.attempting uu____4719  in
      FStar_List.map (wl_prob_to_string wl) uu____4716  in
    FStar_All.pipe_right uu____4712 (FStar_String.concat "\n\t")
  
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee  -> true 
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee  -> match projectee with | Flex _0 -> _0 
let (flex_reason : flex_t -> Prims.string) =
  fun uu____4813  ->
    match uu____4813 with
    | Flex (uu____4815,u,uu____4817) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4824  ->
    match uu____4824 with
    | Flex (uu____4826,c,args) ->
        let uu____4829 = print_ctx_uvar c  in
        let uu____4831 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4829 uu____4831
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4841 = FStar_Syntax_Util.head_and_args t  in
    match uu____4841 with
    | (head1,_args) ->
        let uu____4885 =
          let uu____4886 = FStar_Syntax_Subst.compress head1  in
          uu____4886.FStar_Syntax_Syntax.n  in
        (match uu____4885 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4890 -> true
         | uu____4904 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4912 = FStar_Syntax_Util.head_and_args t  in
    match uu____4912 with
    | (head1,_args) ->
        let uu____4955 =
          let uu____4956 = FStar_Syntax_Subst.compress head1  in
          uu____4956.FStar_Syntax_Syntax.n  in
        (match uu____4955 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4960) -> u
         | uu____4977 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5002 = FStar_Syntax_Util.head_and_args t  in
      match uu____5002 with
      | (head1,args) ->
          let uu____5049 =
            let uu____5050 = FStar_Syntax_Subst.compress head1  in
            uu____5050.FStar_Syntax_Syntax.n  in
          (match uu____5049 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5058)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5091 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5116  ->
                         match uu___18_5116 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5121 =
                               let uu____5122 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5122.FStar_Syntax_Syntax.n  in
                             (match uu____5121 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5127 -> false)
                         | uu____5129 -> true))
                  in
               (match uu____5091 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5154 =
                        FStar_List.collect
                          (fun uu___19_5166  ->
                             match uu___19_5166 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5170 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5170]
                             | uu____5171 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5154 FStar_List.rev  in
                    let uu____5194 =
                      let uu____5201 =
                        let uu____5210 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5232  ->
                                  match uu___20_5232 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5236 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5236]
                                  | uu____5237 -> []))
                           in
                        FStar_All.pipe_right uu____5210 FStar_List.rev  in
                      let uu____5260 =
                        let uu____5263 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5263  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5201 uu____5260
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5194 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5299  ->
                                match uu____5299 with
                                | (x,i) ->
                                    let uu____5318 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5318, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5349  ->
                                match uu____5349 with
                                | (a,i) ->
                                    let uu____5368 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5368, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((Flex (t1, v1, all_args)), wl1))))
           | uu____5390 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5412 =
          let uu____5435 =
            let uu____5436 = FStar_Syntax_Subst.compress k  in
            uu____5436.FStar_Syntax_Syntax.n  in
          match uu____5435 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5518 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5518)
              else
                (let uu____5553 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5553 with
                 | (ys',t1,uu____5586) ->
                     let uu____5591 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5591))
          | uu____5630 ->
              let uu____5631 =
                let uu____5636 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5636)  in
              ((ys, t), uu____5631)
           in
        match uu____5412 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____5731 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5731 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____5809 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5809
                then
                  let uu____5814 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5816 = print_ctx_uvar uv  in
                  let uu____5818 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5814 uu____5816 uu____5818
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5827 =
                   let uu____5829 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5829  in
                 let uu____5832 =
                   let uu____5835 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5835
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5827 uu____5832 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5868 =
               let uu____5869 =
                 let uu____5871 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5873 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5871 uu____5873
                  in
               failwith uu____5869  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5939  ->
                       match uu____5939 with
                       | (a,i) ->
                           let uu____5960 =
                             let uu____5961 = FStar_Syntax_Subst.compress a
                                in
                             uu____5961.FStar_Syntax_Syntax.n  in
                           (match uu____5960 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5987 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5997 =
                 let uu____5999 = is_flex g  in Prims.op_Negation uu____5999
                  in
               if uu____5997
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6008 = destruct_flex_t g wl  in
                  match uu____6008 with
                  | (Flex (uu____6013,uv1,args),wl1) ->
                      ((let uu____6018 = args_as_binders args  in
                        assign_solution uu____6018 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___748_6020 = wl1  in
              {
                attempting = (uu___748_6020.attempting);
                wl_deferred = (uu___748_6020.wl_deferred);
                wl_deferred_to_tac = (uu___748_6020.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___748_6020.defer_ok);
                smt_ok = (uu___748_6020.smt_ok);
                umax_heuristic_ok = (uu___748_6020.umax_heuristic_ok);
                tcenv = (uu___748_6020.tcenv);
                wl_implicits = (uu___748_6020.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6045 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6045
         then
           let uu____6050 = FStar_Util.string_of_int pid  in
           let uu____6052 =
             let uu____6054 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6054 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6050 uu____6052
         else ());
        commit sol;
        (let uu___756_6068 = wl  in
         {
           attempting = (uu___756_6068.attempting);
           wl_deferred = (uu___756_6068.wl_deferred);
           wl_deferred_to_tac = (uu___756_6068.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___756_6068.defer_ok);
           smt_ok = (uu___756_6068.smt_ok);
           umax_heuristic_ok = (uu___756_6068.umax_heuristic_ok);
           tcenv = (uu___756_6068.tcenv);
           wl_implicits = (uu___756_6068.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let uu____6104 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6104
           then
             let uu____6109 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6113 =
               let uu____6115 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6115 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6109 uu____6113
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____6150 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6150 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____6190 = occurs uk t  in
      match uu____6190 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6229 =
                 let uu____6231 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6233 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6231 uu____6233
                  in
               FStar_Pervasives_Native.Some uu____6229)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____6353 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6353 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6404 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6461  ->
             match uu____6461 with
             | (x,uu____6473) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6491 = FStar_List.last bs  in
      match uu____6491 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6515) ->
          let uu____6526 =
            FStar_Util.prefix_until
              (fun uu___21_6541  ->
                 match uu___21_6541 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6544 -> false) g
             in
          (match uu____6526 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6558,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6595 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6595 with
        | (pfx,uu____6605) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6617 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6617 with
             | (uu____6625,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6739 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6740 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6804  ->
                  fun uu____6805  ->
                    match (uu____6804, uu____6805) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6908 =
                          let uu____6910 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6910
                           in
                        if uu____6908
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6944 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6944
                           then
                             let uu____6961 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6961)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6740 with | (isect,uu____7011) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7047 'Auu____7048 .
    (FStar_Syntax_Syntax.bv * 'Auu____7047) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7048) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7106  ->
              fun uu____7107  ->
                match (uu____7106, uu____7107) with
                | ((a,uu____7126),(b,uu____7128)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7144 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7144) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7175  ->
           match uu____7175 with
           | (y,uu____7182) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7192 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7192) Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____7354 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7354
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7387 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____7439 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7483 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7504 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7512  ->
    match uu___22_7512 with
    | MisMatch (d1,d2) ->
        let uu____7524 =
          let uu____7526 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7528 =
            let uu____7530 =
              let uu____7532 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7532 ")"  in
            Prims.op_Hat ") (" uu____7530  in
          Prims.op_Hat uu____7526 uu____7528  in
        Prims.op_Hat "MisMatch (" uu____7524
    | HeadMatch u ->
        let uu____7539 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7539
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7548  ->
    match uu___23_7548 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7565 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7587 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7587 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7598 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____7622 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7632 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7651 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7651
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7652 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7653 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7654 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7667 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7681 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7705) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7711,uu____7712) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7754) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7779;
             FStar_Syntax_Syntax.index = uu____7780;
             FStar_Syntax_Syntax.sort = t2;_},uu____7782)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7790 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7791 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7792 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7807 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7814 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7834 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7834
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7853;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7854;
             FStar_Syntax_Syntax.ltyp = uu____7855;
             FStar_Syntax_Syntax.rng = uu____7856;_},uu____7857)
            ->
            let uu____7868 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7868 t21
        | (uu____7869,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7870;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7871;
             FStar_Syntax_Syntax.ltyp = uu____7872;
             FStar_Syntax_Syntax.rng = uu____7873;_})
            ->
            let uu____7884 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7884
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7896 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7896
            then FullMatch
            else
              (let uu____7901 =
                 let uu____7910 =
                   let uu____7913 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7913  in
                 let uu____7914 =
                   let uu____7917 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7917  in
                 (uu____7910, uu____7914)  in
               MisMatch uu____7901)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7923),FStar_Syntax_Syntax.Tm_uinst (g,uu____7925)) ->
            let uu____7934 = head_matches env f g  in
            FStar_All.pipe_right uu____7934 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7935) -> HeadMatch true
        | (uu____7937,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7941 = FStar_Const.eq_const c d  in
            if uu____7941
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7951),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7953)) ->
            let uu____7986 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7986
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7996),FStar_Syntax_Syntax.Tm_refine (y,uu____7998)) ->
            let uu____8007 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8007 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8009),uu____8010) ->
            let uu____8015 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8015 head_match
        | (uu____8016,FStar_Syntax_Syntax.Tm_refine (x,uu____8018)) ->
            let uu____8023 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8023 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8024,FStar_Syntax_Syntax.Tm_type
           uu____8025) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8027,FStar_Syntax_Syntax.Tm_arrow uu____8028) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8059),FStar_Syntax_Syntax.Tm_app (head',uu____8061))
            ->
            let uu____8110 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8110 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8112),uu____8113) ->
            let uu____8138 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8138 head_match
        | (uu____8139,FStar_Syntax_Syntax.Tm_app (head1,uu____8141)) ->
            let uu____8166 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8166 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8167,FStar_Syntax_Syntax.Tm_let
           uu____8168) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8196,FStar_Syntax_Syntax.Tm_match uu____8197) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8243,FStar_Syntax_Syntax.Tm_abs
           uu____8244) -> HeadMatch true
        | uu____8282 ->
            let uu____8287 =
              let uu____8296 = delta_depth_of_term env t11  in
              let uu____8299 = delta_depth_of_term env t21  in
              (uu____8296, uu____8299)  in
            MisMatch uu____8287
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head1 =
              let uu____8368 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8368  in
            (let uu____8370 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8370
             then
               let uu____8375 = FStar_Syntax_Print.term_to_string t  in
               let uu____8377 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8375 uu____8377
             else ());
            (let uu____8382 =
               let uu____8383 = FStar_Syntax_Util.un_uinst head1  in
               uu____8383.FStar_Syntax_Syntax.n  in
             match uu____8382 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8389 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8389 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8403 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8403
                        then
                          let uu____8408 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8408
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8413 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota]  in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps
                         in
                      let t' =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t
                         in
                      let uu____8431 =
                        let uu____8433 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8433 = FStar_Syntax_Util.Equal  in
                      if uu____8431
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8440 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8440
                          then
                            let uu____8445 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8447 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8445
                              uu____8447
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8452 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry1 n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8604 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8604
             then
               let uu____8609 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8611 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8613 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8609
                 uu____8611 uu____8613
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8641 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____8641 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8689 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8689 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8727),uu____8728)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8749 =
                      let uu____8758 = maybe_inline t11  in
                      let uu____8761 = maybe_inline t21  in
                      (uu____8758, uu____8761)  in
                    match uu____8749 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8804,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8805))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8826 =
                      let uu____8835 = maybe_inline t11  in
                      let uu____8838 = maybe_inline t21  in
                      (uu____8835, uu____8838)  in
                    match uu____8826 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8893 -> fail1 n_delta r t11 t21
             | uu____8902 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8917 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8917
           then
             let uu____8922 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8924 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8926 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8934 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8951 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8951
                    (fun uu____8986  ->
                       match uu____8986 with
                       | (t11,t21) ->
                           let uu____8994 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8996 =
                             let uu____8998 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8998  in
                           Prims.op_Hat uu____8994 uu____8996))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8922 uu____8924 uu____8926 uu____8934
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9015 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9015 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9030  ->
    match uu___24_9030 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___1245_9079 = p  in
      let uu____9082 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9083 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1245_9079.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9082;
        FStar_TypeChecker_Common.relation =
          (uu___1245_9079.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9083;
        FStar_TypeChecker_Common.element =
          (uu___1245_9079.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1245_9079.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1245_9079.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1245_9079.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1245_9079.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1245_9079.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9098 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9098
            (fun _9103  -> FStar_TypeChecker_Common.TProb _9103)
      | FStar_TypeChecker_Common.CProb uu____9104 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9127 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9127 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9135 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9135 with
           | (lh,lhs_args) ->
               let uu____9182 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9182 with
                | (rh,rhs_args) ->
                    let uu____9229 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9242,FStar_Syntax_Syntax.Tm_uvar uu____9243)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9332 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9359,uu____9360)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9375,FStar_Syntax_Syntax.Tm_uvar uu____9376)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9391,FStar_Syntax_Syntax.Tm_arrow uu____9392)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9422 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9422.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9422.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9422.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9422.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9422.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9422.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9422.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9422.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9422.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9425,FStar_Syntax_Syntax.Tm_type uu____9426)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9442 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9442.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9442.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9442.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9442.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9442.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9442.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9442.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9442.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9442.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9445,FStar_Syntax_Syntax.Tm_uvar uu____9446)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9462 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9462.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9462.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9462.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9462.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9462.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9462.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9462.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9462.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9462.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9465,FStar_Syntax_Syntax.Tm_uvar uu____9466)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9481,uu____9482)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9497,FStar_Syntax_Syntax.Tm_uvar uu____9498)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9513,uu____9514) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9229 with
                     | (rank,tp1) ->
                         let uu____9527 =
                           FStar_All.pipe_right
                             (let uu___1316_9531 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1316_9531.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1316_9531.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1316_9531.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1316_9531.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1316_9531.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1316_9531.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1316_9531.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1316_9531.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1316_9531.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9534  ->
                                FStar_TypeChecker_Common.TProb _9534)
                            in
                         (rank, uu____9527))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9538 =
            FStar_All.pipe_right
              (let uu___1320_9542 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1320_9542.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1320_9542.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1320_9542.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1320_9542.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1320_9542.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1320_9542.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1320_9542.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1320_9542.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1320_9542.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9545  -> FStar_TypeChecker_Common.CProb _9545)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9538)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9605 probs =
      match uu____9605 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9686 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9707 = rank wl.tcenv hd1  in
               (match uu____9707 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____9768 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9773 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9773)
                          in
                       if uu____9768
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____9846 = FStar_Syntax_Util.head_and_args t  in
          match uu____9846 with
          | (hd1,uu____9865) ->
              let uu____9890 =
                let uu____9891 = FStar_Syntax_Subst.compress hd1  in
                uu____9891.FStar_Syntax_Syntax.n  in
              (match uu____9890 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9896) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9931  ->
                           match uu____9931 with
                           | (y,uu____9940) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9963  ->
                                       match uu____9963 with
                                       | (x,uu____9972) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9977 -> false)
           in
        let uu____9979 = rank tcenv p  in
        match uu____9979 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9988 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____10069 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10088 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10107 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10124 = FStar_Thunk.mkv s  in UFailed uu____10124 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10139 = FStar_Thunk.mk s  in UFailed uu____10139 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____10191 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10191 with
                        | (k,uu____10199) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10212 -> false)))
            | uu____10214 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10266 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10274 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10274 = Prims.int_zero))
                           in
                        if uu____10266 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10295 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10303 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10303 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10295)
               in
            let uu____10307 = filter1 u12  in
            let uu____10310 = filter1 u22  in (uu____10307, uu____10310)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10345 = filter_out_common_univs us1 us2  in
                   (match uu____10345 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10405 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10405 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10408 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10425  ->
                               let uu____10426 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10428 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10426 uu____10428))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10454 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10454 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10480 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10480 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10483 ->
                   ufailed_thunk
                     (fun uu____10494  ->
                        let uu____10495 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10497 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10495 uu____10497 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10500,uu____10501) ->
              let uu____10503 =
                let uu____10505 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10507 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10505 uu____10507
                 in
              failwith uu____10503
          | (FStar_Syntax_Syntax.U_unknown ,uu____10510) ->
              let uu____10511 =
                let uu____10513 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10515 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10513 uu____10515
                 in
              failwith uu____10511
          | (uu____10518,FStar_Syntax_Syntax.U_bvar uu____10519) ->
              let uu____10521 =
                let uu____10523 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10525 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10523 uu____10525
                 in
              failwith uu____10521
          | (uu____10528,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10529 =
                let uu____10531 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10533 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10531 uu____10533
                 in
              failwith uu____10529
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10563 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10563
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10580 = occurs_univ v1 u3  in
              if uu____10580
              then
                let uu____10583 =
                  let uu____10585 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10587 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10585 uu____10587
                   in
                try_umax_components u11 u21 uu____10583
              else
                (let uu____10592 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10592)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10604 = occurs_univ v1 u3  in
              if uu____10604
              then
                let uu____10607 =
                  let uu____10609 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10611 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10609 uu____10611
                   in
                try_umax_components u11 u21 uu____10607
              else
                (let uu____10616 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10616)
          | (FStar_Syntax_Syntax.U_max uu____10617,uu____10618) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10626 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10626
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10632,FStar_Syntax_Syntax.U_max uu____10633) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10641 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10641
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10647,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10649,FStar_Syntax_Syntax.U_name uu____10650) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10652) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10654) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10656,FStar_Syntax_Syntax.U_succ uu____10657) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10659,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1  ->
    fun bc2  ->
      let uu____10766 = bc1  in
      match uu____10766 with
      | (bs1,mk_cod1) ->
          let uu____10810 = bc2  in
          (match uu____10810 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10921 = aux xs ys  in
                     (match uu____10921 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11004 =
                       let uu____11011 = mk_cod1 xs  in ([], uu____11011)  in
                     let uu____11014 =
                       let uu____11021 = mk_cod2 ys  in ([], uu____11021)  in
                     (uu____11004, uu____11014)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____11090 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11090 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11093 =
                    let uu____11094 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11094 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11093
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11099 = has_type_guard t1 t2  in (uu____11099, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11100 = has_type_guard t2 t1  in (uu____11100, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11107  ->
    match uu___25_11107 with
    | Flex (uu____11109,uu____11110,[]) -> true
    | uu____11120 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11134 = f  in
      match uu____11134 with
      | Flex (uu____11136,u,uu____11138) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11162 = f  in
      match uu____11162 with
      | Flex
          (uu____11169,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11170;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11171;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11174;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11175;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11176;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11177;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11241  ->
                 match uu____11241 with
                 | (y,uu____11250) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11404 =
                  let uu____11419 =
                    let uu____11422 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11422  in
                  ((FStar_List.rev pat_binders), uu____11419)  in
                FStar_Pervasives_Native.Some uu____11404
            | (uu____11455,[]) ->
                let uu____11486 =
                  let uu____11501 =
                    let uu____11504 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11504  in
                  ((FStar_List.rev pat_binders), uu____11501)  in
                FStar_Pervasives_Native.Some uu____11486
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11595 =
                  let uu____11596 = FStar_Syntax_Subst.compress a  in
                  uu____11596.FStar_Syntax_Syntax.n  in
                (match uu____11595 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11616 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11616
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1657_11646 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1657_11646.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1657_11646.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11650 =
                            let uu____11651 =
                              let uu____11658 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11658)  in
                            FStar_Syntax_Syntax.NT uu____11651  in
                          [uu____11650]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1663_11674 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1663_11674.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1663_11674.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11675 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11715 =
                  let uu____11722 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11722  in
                (match uu____11715 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11781 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11806 ->
               let uu____11807 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11807 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12139 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12139
       then
         let uu____12144 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12144
       else ());
      (let uu____12150 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12150
       then
         let uu____12155 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12155
       else ());
      (let uu____12160 = next_prob probs  in
       match uu____12160 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1690_12187 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1690_12187.wl_deferred);
               wl_deferred_to_tac = (uu___1690_12187.wl_deferred_to_tac);
               ctr = (uu___1690_12187.ctr);
               defer_ok = (uu___1690_12187.defer_ok);
               smt_ok = (uu___1690_12187.smt_ok);
               umax_heuristic_ok = (uu___1690_12187.umax_heuristic_ok);
               tcenv = (uu___1690_12187.tcenv);
               wl_implicits = (uu___1690_12187.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12196 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12196
                 then
                   let uu____12199 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12199
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       maybe_defer_to_user_tac env tp
                         "deferring flex_rigid or flex_flex subtyping" probs1
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1702_12211 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1702_12211.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1702_12211.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1702_12211.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1702_12211.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1702_12211.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1702_12211.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1702_12211.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1702_12211.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1702_12211.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12231 =
                  let uu____12238 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12238, (probs.wl_implicits))  in
                Success uu____12231
            | uu____12244 ->
                let uu____12254 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12319  ->
                          match uu____12319 with
                          | (c,uu____12329,uu____12330) -> c < probs.ctr))
                   in
                (match uu____12254 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12378 =
                            let uu____12385 = as_deferred probs.wl_deferred
                               in
                            let uu____12386 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12385, uu____12386, (probs.wl_implicits))
                             in
                          Success uu____12378
                      | uu____12387 ->
                          let uu____12397 =
                            let uu___1716_12398 = probs  in
                            let uu____12399 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12420  ->
                                      match uu____12420 with
                                      | (uu____12428,uu____12429,y) -> y))
                               in
                            {
                              attempting = uu____12399;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1716_12398.wl_deferred_to_tac);
                              ctr = (uu___1716_12398.ctr);
                              defer_ok = (uu___1716_12398.defer_ok);
                              smt_ok = (uu___1716_12398.smt_ok);
                              umax_heuristic_ok =
                                (uu___1716_12398.umax_heuristic_ok);
                              tcenv = (uu___1716_12398.tcenv);
                              wl_implicits = (uu___1716_12398.wl_implicits)
                            }  in
                          solve env uu____12397))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____12438 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12438 with
            | USolved wl1 ->
                let uu____12440 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12440
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12443 = defer_lit "" orig wl1  in
                solve env uu____12443

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____12494 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12494 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12497 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12510;
                  FStar_Syntax_Syntax.vars = uu____12511;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12514;
                  FStar_Syntax_Syntax.vars = uu____12515;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12528,uu____12529) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12537,FStar_Syntax_Syntax.Tm_uinst uu____12538) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12546 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12557 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12557
              then
                let uu____12562 = prob_to_string env orig  in
                let uu____12564 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12562 uu____12564
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun reason  ->
        fun wl  ->
          let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl  in
          let wl2 =
            let uu___1798_12579 = wl1  in
            let uu____12580 =
              let uu____12590 =
                let uu____12598 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12598, orig)  in
              uu____12590 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1798_12579.attempting);
              wl_deferred = (uu___1798_12579.wl_deferred);
              wl_deferred_to_tac = uu____12580;
              ctr = (uu___1798_12579.ctr);
              defer_ok = (uu___1798_12579.defer_ok);
              smt_ok = (uu___1798_12579.smt_ok);
              umax_heuristic_ok = (uu___1798_12579.umax_heuristic_ok);
              tcenv = (uu___1798_12579.tcenv);
              wl_implicits = (uu___1798_12579.wl_implicits)
            }  in
          solve env wl2

and (maybe_defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun prob  ->
      fun reason  ->
        fun wl  ->
          match prob.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ  ->
              let should_defer_tac t =
                let uu____12627 = FStar_Syntax_Util.head_and_args t  in
                match uu____12627 with
                | (head1,uu____12651) ->
                    let uu____12676 =
                      let uu____12677 = FStar_Syntax_Subst.compress head1  in
                      uu____12677.FStar_Syntax_Syntax.n  in
                    (match uu____12676 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12687) ->
                         let uu____12704 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12704,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12708 -> (false, ""))
                 in
              let uu____12713 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12713 with
               | (l1,r1) ->
                   let uu____12726 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12726 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12743 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12743)))
          | uu____12744 ->
              let uu____12745 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12745

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____12831 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12831 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12886 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12886
                then
                  let uu____12891 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12893 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12891 uu____12893
                else ());
               (let uu____12898 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12898 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12944 = eq_prob t1 t2 wl2  in
                         (match uu____12944 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12965 ->
                         let uu____12974 = eq_prob t1 t2 wl2  in
                         (match uu____12974 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13024 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13039 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13040 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13039, uu____13040)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13045 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13046 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13045, uu____13046)
                            in
                         (match uu____13024 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13077 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13077 with
                                | (t1_hd,t1_args) ->
                                    let uu____13122 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13122 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13188 =
                                              let uu____13195 =
                                                let uu____13206 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13206 :: t1_args  in
                                              let uu____13223 =
                                                let uu____13232 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13232 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13281  ->
                                                   fun uu____13282  ->
                                                     fun uu____13283  ->
                                                       match (uu____13281,
                                                               uu____13282,
                                                               uu____13283)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13333),
                                                          (a2,uu____13335))
                                                           ->
                                                           let uu____13372 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13372
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13195
                                                uu____13223
                                               in
                                            match uu____13188 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1901_13398 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1901_13398.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1901_13398.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1901_13398.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1901_13398.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13409 =
                                                  solve env1 wl'  in
                                                (match uu____13409 with
                                                 | Success
                                                     (uu____13412,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13416 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13416))
                                                 | Failed uu____13417 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13449 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13449 with
                                | (t1_base,p1_opt) ->
                                    let uu____13485 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13485 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13584 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13584
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____13637 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13637
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13669 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13669
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13701 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13701
                                           | uu____13704 -> t_base  in
                                         let uu____13721 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13721 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13735 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13735, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13742 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13742 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13778 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13778 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13814 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13814
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____13838 = combine t11 t21 wl2  in
                              (match uu____13838 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13871 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13871
                                     then
                                       let uu____13876 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13876
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13918 ts1 =
               match uu____13918 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13981 = pairwise out t wl2  in
                        (match uu____13981 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14017 =
               let uu____14028 = FStar_List.hd ts  in (uu____14028, [], wl1)
                in
             let uu____14037 = FStar_List.tl ts  in
             aux uu____14017 uu____14037  in
           let uu____14044 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14044 with
           | (this_flex,this_rigid) ->
               let uu____14070 =
                 let uu____14071 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14071.FStar_Syntax_Syntax.n  in
               (match uu____14070 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14096 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14096
                    then
                      let uu____14099 = destruct_flex_t this_flex wl  in
                      (match uu____14099 with
                       | (flex,wl1) ->
                           let uu____14106 = quasi_pattern env flex  in
                           (match uu____14106 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14125 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14125
                                  then
                                    let uu____14130 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14130
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14137 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2011_14140 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2011_14140.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2011_14140.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2011_14140.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2011_14140.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2011_14140.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2011_14140.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2011_14140.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2011_14140.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2011_14140.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14137)
                | uu____14141 ->
                    ((let uu____14143 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14143
                      then
                        let uu____14148 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14148
                      else ());
                     (let uu____14153 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14153 with
                      | (u,_args) ->
                          let uu____14196 =
                            let uu____14197 = FStar_Syntax_Subst.compress u
                               in
                            uu____14197.FStar_Syntax_Syntax.n  in
                          (match uu____14196 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14225 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14225 with
                                 | (u',uu____14244) ->
                                     let uu____14269 =
                                       let uu____14270 = whnf env u'  in
                                       uu____14270.FStar_Syntax_Syntax.n  in
                                     (match uu____14269 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14292 -> false)
                                  in
                               let uu____14294 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14317  ->
                                         match uu___26_14317 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____14331 -> false)
                                         | uu____14335 -> false))
                                  in
                               (match uu____14294 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14350 = whnf env this_rigid
                                         in
                                      let uu____14351 =
                                        FStar_List.collect
                                          (fun uu___27_14357  ->
                                             match uu___27_14357 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14363 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14363]
                                             | uu____14367 -> [])
                                          bounds_probs
                                         in
                                      uu____14350 :: uu____14351  in
                                    let uu____14368 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14368 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14401 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14416 =
                                               let uu____14417 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14417.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14416 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14429 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14429)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14440 -> bound  in
                                           let uu____14441 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14441)  in
                                         (match uu____14401 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14476 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14476
                                                then
                                                  let wl'1 =
                                                    let uu___2071_14482 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2071_14482.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2071_14482.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2071_14482.ctr);
                                                      defer_ok =
                                                        (uu___2071_14482.defer_ok);
                                                      smt_ok =
                                                        (uu___2071_14482.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2071_14482.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2071_14482.tcenv);
                                                      wl_implicits =
                                                        (uu___2071_14482.wl_implicits)
                                                    }  in
                                                  let uu____14483 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14483
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14489 =
                                                  solve_t env eq_prob
                                                    (let uu___2076_14491 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2076_14491.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2076_14491.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2076_14491.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2076_14491.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2076_14491.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2076_14491.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14489 with
                                                | Success
                                                    (uu____14493,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2083_14497 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2083_14497.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2083_14497.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2083_14497.ctr);
                                                        defer_ok =
                                                          (uu___2083_14497.defer_ok);
                                                        smt_ok =
                                                          (uu___2083_14497.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2083_14497.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2083_14497.tcenv);
                                                        wl_implicits =
                                                          (uu___2083_14497.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      extend_wl wl2
                                                        defer_to_tac imps
                                                       in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3
                                                       in
                                                    let uu____14514 =
                                                      FStar_List.fold_left
                                                        (fun wl5  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p,msg) ->
                                                    ((let uu____14526 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14526
                                                      then
                                                        let uu____14531 =
                                                          let uu____14533 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14533
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14531
                                                      else ());
                                                     (let uu____14546 =
                                                        let uu____14561 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14561)
                                                         in
                                                      match uu____14546 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14583))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14609 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14609
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2
                                                                     in
                                                                  let uu____14629
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14629))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14654 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14654
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____14674
                                                                    =
                                                                    let uu____14679
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14679
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14674
                                                                    [] wl2
                                                                     in
                                                                  let uu____14685
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14685))))
                                                      | uu____14686 ->
                                                          let uu____14701 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14701 p)))))))
                           | uu____14708 when flip ->
                               let uu____14709 =
                                 let uu____14711 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14713 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14711 uu____14713
                                  in
                               failwith uu____14709
                           | uu____14716 ->
                               let uu____14717 =
                                 let uu____14719 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14721 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14719 uu____14721
                                  in
                               failwith uu____14717)))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14757  ->
                         match uu____14757 with
                         | (x,i) ->
                             let uu____14776 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14776, i)) bs_lhs
                     in
                  let uu____14779 = lhs  in
                  match uu____14779 with
                  | Flex (uu____14780,u_lhs,uu____14782) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14879 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14889 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14889, univ)
                             in
                          match uu____14879 with
                          | (k,univ) ->
                              let uu____14896 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14896 with
                               | (uu____14913,u,wl3) ->
                                   let uu____14916 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14916, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14942 =
                              let uu____14955 =
                                let uu____14966 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14966 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15017  ->
                                   fun uu____15018  ->
                                     match (uu____15017, uu____15018) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15119 =
                                           let uu____15126 =
                                             let uu____15129 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15129
                                              in
                                           copy_uvar u_lhs [] uu____15126 wl2
                                            in
                                         (match uu____15119 with
                                          | (uu____15158,t_a,wl3) ->
                                              let uu____15161 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15161 with
                                               | (uu____15180,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14955
                                ([], wl1)
                               in
                            (match uu____14942 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2196_15236 = ct  in
                                   let uu____15237 =
                                     let uu____15240 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15240
                                      in
                                   let uu____15255 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2196_15236.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2196_15236.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15237;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15255;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2196_15236.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2199_15273 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2199_15273.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2199_15273.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15276 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15276 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15314 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15314 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15325 =
                                          let uu____15330 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15330)  in
                                        TERM uu____15325  in
                                      let uu____15331 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15331 with
                                       | (sub_prob,wl3) ->
                                           let uu____15345 =
                                             let uu____15346 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15346
                                              in
                                           solve env uu____15345))
                             | (x,imp)::formals2 ->
                                 let uu____15368 =
                                   let uu____15375 =
                                     let uu____15378 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15378
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15375 wl1
                                    in
                                 (match uu____15368 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15399 =
                                          let uu____15402 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15402
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15399 u_x
                                         in
                                      let uu____15403 =
                                        let uu____15406 =
                                          let uu____15409 =
                                            let uu____15410 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15410, imp)  in
                                          [uu____15409]  in
                                        FStar_List.append bs_terms
                                          uu____15406
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15403 formals2 wl2)
                              in
                           let uu____15437 = occurs_check u_lhs arrow1  in
                           (match uu____15437 with
                            | (uu____15450,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15466 =
                                    FStar_Thunk.mk
                                      (fun uu____15470  ->
                                         let uu____15471 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15471)
                                     in
                                  giveup_or_defer env orig wl uu____15466
                                else aux [] [] formals wl))

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob * worklist))
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____15504 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15504
               then
                 let uu____15509 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15512 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15509 (rel_to_string (p_rel orig)) uu____15512
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15643 = rhs wl1 scope env1 subst1  in
                     (match uu____15643 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15666 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15666
                            then
                              let uu____15671 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15671
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15749 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15749 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2269_15751 = hd1  in
                       let uu____15752 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2269_15751.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2269_15751.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15752
                       }  in
                     let hd21 =
                       let uu___2272_15756 = hd2  in
                       let uu____15757 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2272_15756.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2272_15756.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15757
                       }  in
                     let uu____15760 =
                       let uu____15765 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15765
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15760 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15788 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15788
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15795 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15795 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15867 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15867
                                  in
                               ((let uu____15885 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15885
                                 then
                                   let uu____15890 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15892 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15890
                                     uu____15892
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15927 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15963 = aux wl [] env [] bs1 bs2  in
               match uu____15963 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16022 = attempt sub_probs wl2  in
                   solve env1 uu____16022)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2310_16042 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2310_16042.wl_deferred_to_tac);
              ctr = (uu___2310_16042.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2310_16042.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16054 = try_solve env wl'  in
          match uu____16054 with
          | Success (uu____16055,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16068 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16068 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let uu____16074 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16074
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16087 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16087 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16121 = lhs1  in
                 match uu____16121 with
                 | Flex (uu____16124,ctx_u,uu____16126) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16134 ->
                           let uu____16135 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16135 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16184 = quasi_pattern env1 lhs1  in
                 match uu____16184 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16218) ->
                     let uu____16223 = lhs1  in
                     (match uu____16223 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16238 = occurs_check ctx_u rhs1  in
                          (match uu____16238 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16289 =
                                   let uu____16297 =
                                     let uu____16299 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16299
                                      in
                                   FStar_Util.Inl uu____16297  in
                                 (uu____16289, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16327 =
                                    let uu____16329 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16329  in
                                  if uu____16327
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16356 =
                                       let uu____16364 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16364  in
                                     let uu____16370 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16356, uu____16370)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16414 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16414 with
                 | (rhs_hd,args) ->
                     let uu____16457 = FStar_Util.prefix args  in
                     (match uu____16457 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16529 = lhs1  in
                          (match uu____16529 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16533 =
                                 let uu____16544 =
                                   let uu____16551 =
                                     let uu____16554 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16554
                                      in
                                   copy_uvar u_lhs [] uu____16551 wl1  in
                                 match uu____16544 with
                                 | (uu____16581,t_last_arg,wl2) ->
                                     let uu____16584 =
                                       let uu____16591 =
                                         let uu____16592 =
                                           let uu____16601 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16601]  in
                                         FStar_List.append bs_lhs uu____16592
                                          in
                                       copy_uvar u_lhs uu____16591 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16584 with
                                      | (uu____16636,lhs',wl3) ->
                                          let uu____16639 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16639 with
                                           | (uu____16656,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16533 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16677 =
                                        let uu____16678 =
                                          let uu____16683 =
                                            let uu____16684 =
                                              let uu____16687 =
                                                let uu____16692 =
                                                  let uu____16693 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16693]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16692
                                                 in
                                              uu____16687
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16684
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16683)  in
                                        TERM uu____16678  in
                                      [uu____16677]  in
                                    let uu____16718 =
                                      let uu____16725 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16725 with
                                      | (p1,wl3) ->
                                          let uu____16745 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16745 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16718 with
                                     | (sub_probs,wl3) ->
                                         let uu____16777 =
                                           let uu____16778 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16778  in
                                         solve env1 uu____16777))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16812 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16812 with
                   | (uu____16830,args) ->
                       (match args with | [] -> false | uu____16866 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16885 =
                     let uu____16886 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16886.FStar_Syntax_Syntax.n  in
                   match uu____16885 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16890 -> true
                   | uu____16906 -> false  in
                 let uu____16908 = quasi_pattern env1 lhs1  in
                 match uu____16908 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       FStar_Thunk.mk
                         (fun uu____16926  ->
                            let uu____16927 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16927)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16936 = is_app rhs1  in
                     if uu____16936
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16941 = is_arrow rhs1  in
                        if uu____16941
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             FStar_Thunk.mk
                               (fun uu____16953  ->
                                  let uu____16954 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16954)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16958 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16958
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____16964 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16964
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____16969 = lhs  in
                   (match uu____16969 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____16973 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____16973 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____16991 =
                                 let uu____16995 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____16995
                                  in
                               FStar_All.pipe_right uu____16991
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17016 = occurs_check ctx_uv rhs1  in
                             (match uu____17016 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17045 =
                                      let uu____17046 =
                                        let uu____17048 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17048
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17046
                                       in
                                    giveup_or_defer env orig wl uu____17045
                                  else
                                    (let uu____17056 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17056
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17063 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17063
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            FStar_Thunk.mk
                                              (fun uu____17076  ->
                                                 let uu____17077 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17079 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17081 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17077 uu____17079
                                                   uu____17081)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17093 ->
                             if wl.defer_ok
                             then
                               let uu____17097 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17097
                             else
                               (let uu____17102 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17102 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17128 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17128
                                | (FStar_Util.Inl msg,uu____17130) ->
                                    first_order orig env wl lhs rhs))))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____17148 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17148
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17154 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17154
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17159 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17159
                then
                  defer_to_user_tac env orig
                    (Prims.op_Hat (flex_reason lhs)
                       (Prims.op_Hat ", " (flex_reason rhs))) wl
                else
                  if
                    wl.defer_ok &&
                      ((Prims.op_Negation (is_flex_pat lhs)) ||
                         (Prims.op_Negation (is_flex_pat rhs)))
                  then
                    (let uu____17166 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17166)
                  else
                    (let uu____17171 =
                       let uu____17188 = quasi_pattern env lhs  in
                       let uu____17195 = quasi_pattern env rhs  in
                       (uu____17188, uu____17195)  in
                     match uu____17171 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17238 = lhs  in
                         (match uu____17238 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17239;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17241;_},u_lhs,uu____17243)
                              ->
                              let uu____17246 = rhs  in
                              (match uu____17246 with
                               | Flex (uu____17247,u_rhs,uu____17249) ->
                                   let uu____17250 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17250
                                   then
                                     let uu____17257 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17257
                                   else
                                     (let uu____17260 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17260 with
                                      | (ctx_w,(ctx_l,ctx_r)) ->
                                          let gamma_w =
                                            gamma_until
                                              u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                              ctx_w
                                             in
                                          let zs =
                                            intersect_binders gamma_w
                                              (FStar_List.append ctx_l
                                                 binders_lhs)
                                              (FStar_List.append ctx_r
                                                 binders_rhs)
                                             in
                                          let uu____17292 =
                                            let uu____17299 =
                                              let uu____17302 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17302
                                               in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17299
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17292 with
                                           | (uu____17308,w,wl1) ->
                                               let w_app =
                                                 let uu____17314 =
                                                   let uu____17319 =
                                                     FStar_List.map
                                                       (fun uu____17330  ->
                                                          match uu____17330
                                                          with
                                                          | (z,uu____17338)
                                                              ->
                                                              let uu____17343
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17343)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17319
                                                    in
                                                 uu____17314
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17345 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17345
                                                 then
                                                   let uu____17350 =
                                                     let uu____17354 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17356 =
                                                       let uu____17360 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17362 =
                                                         let uu____17366 =
                                                           term_to_string w
                                                            in
                                                         let uu____17368 =
                                                           let uu____17372 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17381 =
                                                             let uu____17385
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17394
                                                               =
                                                               let uu____17398
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17398]
                                                                in
                                                             uu____17385 ::
                                                               uu____17394
                                                              in
                                                           uu____17372 ::
                                                             uu____17381
                                                            in
                                                         uu____17366 ::
                                                           uu____17368
                                                          in
                                                       uu____17360 ::
                                                         uu____17362
                                                        in
                                                     uu____17354 ::
                                                       uu____17356
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17350
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17415 =
                                                       let uu____17420 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17420)
                                                        in
                                                     TERM uu____17415  in
                                                   let uu____17421 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17421
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17429 =
                                                          let uu____17434 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17434)
                                                           in
                                                        TERM uu____17429  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17435 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17435))))))
                     | uu____17436 ->
                         let uu____17453 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17453)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17507 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17507
            then
              let uu____17512 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17514 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17516 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17518 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17512 uu____17514 uu____17516 uu____17518
            else ());
           (let uu____17529 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17529 with
            | (head1,args1) ->
                let uu____17572 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17572 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17642 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17642 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17647 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17647)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17668 =
                         FStar_Thunk.mk
                           (fun uu____17675  ->
                              let uu____17676 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17678 = args_to_string args1  in
                              let uu____17682 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17684 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17676 uu____17678 uu____17682
                                uu____17684)
                          in
                       giveup env1 uu____17668 orig
                     else
                       (let uu____17691 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17696 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17696 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17691
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2582_17700 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2582_17700.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2582_17700.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2582_17700.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2582_17700.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2582_17700.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2582_17700.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2582_17700.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2582_17700.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17710 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17710
                                    else solve env1 wl2))
                        else
                          (let uu____17715 = base_and_refinement env1 t1  in
                           match uu____17715 with
                           | (base1,refinement1) ->
                               let uu____17740 = base_and_refinement env1 t2
                                  in
                               (match uu____17740 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif
                                             then
                                               FStar_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else FStar_List.zip args1 args2
                                              in
                                           let uu____17905 =
                                             FStar_List.fold_right
                                               (fun uu____17945  ->
                                                  fun uu____17946  ->
                                                    match (uu____17945,
                                                            uu____17946)
                                                    with
                                                    | (((a1,uu____17998),
                                                        (a2,uu____18000)),
                                                       (probs,wl3)) ->
                                                        let uu____18049 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18049
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17905 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18092 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18092
                                                 then
                                                   let uu____18097 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18097
                                                 else ());
                                                (let uu____18103 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18103
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3))
                                            in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____18130 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18130 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18146 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18146
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18154 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18154))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18179 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18179 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18195 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18195
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18203 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18203)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18231 =
                                           match uu____18231 with
                                           | (prob,reason) ->
                                               ((let uu____18248 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18248
                                                 then
                                                   let uu____18253 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18255 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18257 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18253 uu____18255
                                                     uu____18257
                                                 else ());
                                                (let uu____18263 =
                                                   let uu____18272 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18275 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18272, uu____18275)
                                                    in
                                                 match uu____18263 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18288 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18288 with
                                                      | (head1',uu____18306)
                                                          ->
                                                          let uu____18331 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18331
                                                           with
                                                           | (head2',uu____18349)
                                                               ->
                                                               let uu____18374
                                                                 =
                                                                 let uu____18379
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18380
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18379,
                                                                   uu____18380)
                                                                  in
                                                               (match uu____18374
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18382
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18382
                                                                    then
                                                                    let uu____18387
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18389
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18391
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18393
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18387
                                                                    uu____18389
                                                                    uu____18391
                                                                    uu____18393
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18398
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2670_18406
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2670_18406.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18408
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18408
                                                                    then
                                                                    let uu____18413
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18413
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18418 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18430 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18430 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18438 =
                                             let uu____18439 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18439.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18438 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18444 -> false  in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when
                                              wl1.smt_ok &&
                                                (Prims.op_Negation
                                                   treat_as_injective)
                                              ->
                                              try_solve_without_smt_or_else
                                                env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____18447 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18450 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2690_18486 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2690_18486.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2690_18486.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2690_18486.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2690_18486.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2690_18486.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2690_18486.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2690_18486.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2690_18486.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18562 = destruct_flex_t scrutinee wl1  in
             match uu____18562 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18573 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18573 with
                  | (xs,pat_term,uu____18589,uu____18590) ->
                      let uu____18595 =
                        FStar_List.fold_left
                          (fun uu____18618  ->
                             fun x  ->
                               match uu____18618 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18639 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18639 with
                                    | (uu____18658,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18595 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18679 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18679 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2731_18696 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2731_18696.wl_deferred_to_tac);
                                    ctr = (uu___2731_18696.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2731_18696.umax_heuristic_ok);
                                    tcenv = (uu___2731_18696.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18707 = solve env1 wl'  in
                                (match uu____18707 with
                                 | Success (uu____18710,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2740_18714 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2740_18714.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2740_18714.wl_deferred_to_tac);
                                         ctr = (uu___2740_18714.ctr);
                                         defer_ok =
                                           (uu___2740_18714.defer_ok);
                                         smt_ok = (uu___2740_18714.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2740_18714.umax_heuristic_ok);
                                         tcenv = (uu___2740_18714.tcenv);
                                         wl_implicits =
                                           (uu___2740_18714.wl_implicits)
                                       }  in
                                     let uu____18715 = solve env1 wl'1  in
                                     (match uu____18715 with
                                      | Success
                                          (uu____18718,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18722 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18722))
                                      | Failed uu____18728 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18734 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18757 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18757
                 then
                   let uu____18762 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18764 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18762 uu____18764
                 else ());
                (let uu____18769 =
                   let uu____18790 =
                     let uu____18799 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18799)  in
                   let uu____18806 =
                     let uu____18815 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18815)  in
                   (uu____18790, uu____18806)  in
                 match uu____18769 with
                 | ((uu____18845,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18848;
                                   FStar_Syntax_Syntax.vars = uu____18849;_}),
                    (s,t)) ->
                     let uu____18920 =
                       let uu____18922 = is_flex scrutinee  in
                       Prims.op_Negation uu____18922  in
                     if uu____18920
                     then
                       ((let uu____18933 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18933
                         then
                           let uu____18938 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18938
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18957 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18957
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18972 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18972
                           then
                             let uu____18977 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18979 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18977 uu____18979
                           else ());
                          (let pat_discriminates uu___28_19004 =
                             match uu___28_19004 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19020;
                                  FStar_Syntax_Syntax.p = uu____19021;_},FStar_Pervasives_Native.None
                                ,uu____19022) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19036;
                                  FStar_Syntax_Syntax.p = uu____19037;_},FStar_Pervasives_Native.None
                                ,uu____19038) -> true
                             | uu____19065 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19168 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19168 with
                                       | (uu____19170,uu____19171,t') ->
                                           let uu____19189 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19189 with
                                            | (FullMatch ,uu____19201) ->
                                                true
                                            | (HeadMatch
                                               uu____19215,uu____19216) ->
                                                true
                                            | uu____19231 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19268 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19268
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19279 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19279 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19367,uu____19368) ->
                                       branches1
                                   | uu____19513 -> branches  in
                                 let uu____19568 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19577 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19577 with
                                        | (p,uu____19581,uu____19582) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19611  -> FStar_Util.Inr _19611)
                                   uu____19568))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19641 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19641 with
                                | (p,uu____19650,e) ->
                                    ((let uu____19669 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19669
                                      then
                                        let uu____19674 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19676 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19674 uu____19676
                                      else ());
                                     (let uu____19681 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19696  -> FStar_Util.Inr _19696)
                                        uu____19681)))))
                 | ((s,t),(uu____19699,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19702;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19703;_}))
                     ->
                     let uu____19772 =
                       let uu____19774 = is_flex scrutinee  in
                       Prims.op_Negation uu____19774  in
                     if uu____19772
                     then
                       ((let uu____19785 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19785
                         then
                           let uu____19790 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19790
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19809 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19809
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19824 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19824
                           then
                             let uu____19829 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19831 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19829 uu____19831
                           else ());
                          (let pat_discriminates uu___28_19856 =
                             match uu___28_19856 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19872;
                                  FStar_Syntax_Syntax.p = uu____19873;_},FStar_Pervasives_Native.None
                                ,uu____19874) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19888;
                                  FStar_Syntax_Syntax.p = uu____19889;_},FStar_Pervasives_Native.None
                                ,uu____19890) -> true
                             | uu____19917 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20020 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20020 with
                                       | (uu____20022,uu____20023,t') ->
                                           let uu____20041 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20041 with
                                            | (FullMatch ,uu____20053) ->
                                                true
                                            | (HeadMatch
                                               uu____20067,uu____20068) ->
                                                true
                                            | uu____20083 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20120 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20120
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20131 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20131 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20219,uu____20220) ->
                                       branches1
                                   | uu____20365 -> branches  in
                                 let uu____20420 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20429 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20429 with
                                        | (p,uu____20433,uu____20434) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20463  -> FStar_Util.Inr _20463)
                                   uu____20420))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20493 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20493 with
                                | (p,uu____20502,e) ->
                                    ((let uu____20521 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20521
                                      then
                                        let uu____20526 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20528 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20526 uu____20528
                                      else ());
                                     (let uu____20533 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20548  -> FStar_Util.Inr _20548)
                                        uu____20533)))))
                 | uu____20549 ->
                     ((let uu____20571 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20571
                       then
                         let uu____20576 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20578 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20576 uu____20578
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20624 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20624
            then
              let uu____20629 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20631 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20633 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20635 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20629 uu____20631 uu____20633 uu____20635
            else ());
           (let uu____20640 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20640 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20671,uu____20672) ->
                     let rec may_relate head3 =
                       let uu____20700 =
                         let uu____20701 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20701.FStar_Syntax_Syntax.n  in
                       match uu____20700 with
                       | FStar_Syntax_Syntax.Tm_name uu____20705 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20707 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20732 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20732 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20734 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20737
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20738 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20741,uu____20742) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20784) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20790) ->
                           may_relate t
                       | uu____20795 -> false  in
                     let uu____20797 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20797 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20810 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20810
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20820 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20820
                          then
                            let uu____20823 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20823 with
                             | (guard,wl2) ->
                                 let uu____20830 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20830)
                          else
                            (let uu____20833 =
                               FStar_Thunk.mk
                                 (fun uu____20840  ->
                                    let uu____20841 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20843 =
                                      let uu____20845 =
                                        let uu____20849 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20849
                                          (fun x  ->
                                             let uu____20856 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20856)
                                         in
                                      FStar_Util.dflt "" uu____20845  in
                                    let uu____20861 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20863 =
                                      let uu____20865 =
                                        let uu____20869 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20869
                                          (fun x  ->
                                             let uu____20876 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20876)
                                         in
                                      FStar_Util.dflt "" uu____20865  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20841 uu____20843 uu____20861
                                      uu____20863)
                                in
                             giveup env1 uu____20833 orig))
                 | (HeadMatch (true ),uu____20882) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20897 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20897 with
                        | (guard,wl2) ->
                            let uu____20904 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20904)
                     else
                       (let uu____20907 =
                          FStar_Thunk.mk
                            (fun uu____20912  ->
                               let uu____20913 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20915 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20913 uu____20915)
                           in
                        giveup env1 uu____20907 orig)
                 | (uu____20918,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2922_20932 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2922_20932.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2922_20932.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2922_20932.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2922_20932.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2922_20932.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2922_20932.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2922_20932.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2922_20932.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20959 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20959
          then
            let uu____20962 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20962
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20968 =
                let uu____20971 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20971  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20968 t1);
             (let uu____20990 =
                let uu____20993 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20993  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20990 t2);
             (let uu____21012 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21012
              then
                let uu____21016 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21018 =
                  let uu____21020 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21022 =
                    let uu____21024 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21024  in
                  Prims.op_Hat uu____21020 uu____21022  in
                let uu____21027 =
                  let uu____21029 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21031 =
                    let uu____21033 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21033  in
                  Prims.op_Hat uu____21029 uu____21031  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21016 uu____21018 uu____21027
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21040,uu____21041) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21057,FStar_Syntax_Syntax.Tm_delayed uu____21058) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21074,uu____21075) ->
                  let uu____21102 =
                    let uu___2953_21103 = problem  in
                    let uu____21104 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2953_21103.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21104;
                      FStar_TypeChecker_Common.relation =
                        (uu___2953_21103.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2953_21103.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2953_21103.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2953_21103.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2953_21103.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2953_21103.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2953_21103.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2953_21103.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21102 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21105,uu____21106) ->
                  let uu____21113 =
                    let uu___2959_21114 = problem  in
                    let uu____21115 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2959_21114.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21115;
                      FStar_TypeChecker_Common.relation =
                        (uu___2959_21114.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2959_21114.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2959_21114.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2959_21114.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2959_21114.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2959_21114.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2959_21114.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2959_21114.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21113 wl
              | (uu____21116,FStar_Syntax_Syntax.Tm_ascribed uu____21117) ->
                  let uu____21144 =
                    let uu___2965_21145 = problem  in
                    let uu____21146 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2965_21145.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2965_21145.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2965_21145.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21146;
                      FStar_TypeChecker_Common.element =
                        (uu___2965_21145.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2965_21145.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2965_21145.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2965_21145.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2965_21145.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2965_21145.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21144 wl
              | (uu____21147,FStar_Syntax_Syntax.Tm_meta uu____21148) ->
                  let uu____21155 =
                    let uu___2971_21156 = problem  in
                    let uu____21157 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2971_21156.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2971_21156.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2971_21156.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21157;
                      FStar_TypeChecker_Common.element =
                        (uu___2971_21156.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2971_21156.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2971_21156.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2971_21156.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2971_21156.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2971_21156.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21155 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21159),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21161)) ->
                  let uu____21170 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21170
              | (FStar_Syntax_Syntax.Tm_bvar uu____21171,uu____21172) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21174,FStar_Syntax_Syntax.Tm_bvar uu____21175) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21245 =
                    match uu___29_21245 with
                    | [] -> c
                    | bs ->
                        let uu____21273 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21273
                     in
                  let uu____21284 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21284 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____21433 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21433
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___30_21522 =
                    match uu___30_21522 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21564 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21564 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21709 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21710 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21709
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21710 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21712,uu____21713) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21744 -> true
                    | uu____21764 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21824 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_21832 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_21832.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_21832.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_21832.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_21832.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_21832.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_21832.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_21832.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_21832.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_21832.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_21832.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_21832.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_21832.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_21832.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_21832.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_21832.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_21832.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_21832.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_21832.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_21832.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_21832.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_21832.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_21832.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_21832.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_21832.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_21832.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_21832.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_21832.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_21832.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_21832.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_21832.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_21832.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_21832.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_21832.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_21832.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_21832.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_21832.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_21832.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_21832.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_21832.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_21832.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_21832.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_21832.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_21832.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_21832.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_21832.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21824 with
                       | (uu____21837,ty,uu____21839) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21848 =
                                 let uu____21849 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21849.FStar_Syntax_Syntax.n  in
                               match uu____21848 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21852 ->
                                   let uu____21859 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21859
                               | uu____21860 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21863 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21863
                             then
                               let uu____21868 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21870 =
                                 let uu____21872 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21872
                                  in
                               let uu____21873 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21868 uu____21870 uu____21873
                             else ());
                            r1))
                     in
                  let uu____21878 =
                    let uu____21895 = maybe_eta t1  in
                    let uu____21902 = maybe_eta t2  in
                    (uu____21895, uu____21902)  in
                  (match uu____21878 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_21944 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_21944.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_21944.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_21944.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_21944.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_21944.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_21944.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_21944.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_21944.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21965 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21965
                       then
                         let uu____21968 = destruct_flex_t not_abs wl  in
                         (match uu____21968 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_21985 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_21985.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_21985.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_21985.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_21985.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_21985.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_21985.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_21985.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_21985.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21988 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21988 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22011 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22011
                       then
                         let uu____22014 = destruct_flex_t not_abs wl  in
                         (match uu____22014 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22031 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22031.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22031.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22031.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22031.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22031.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22031.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22031.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22031.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22034 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22034 orig))
                   | uu____22037 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22055,FStar_Syntax_Syntax.Tm_abs uu____22056) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22087 -> true
                    | uu____22107 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____22167 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_22175 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_22175.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_22175.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_22175.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_22175.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_22175.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_22175.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_22175.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_22175.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_22175.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_22175.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_22175.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_22175.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_22175.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_22175.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_22175.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_22175.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_22175.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_22175.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_22175.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_22175.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_22175.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_22175.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_22175.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_22175.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_22175.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_22175.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_22175.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_22175.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_22175.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_22175.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_22175.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_22175.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_22175.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_22175.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_22175.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_22175.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_22175.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_22175.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_22175.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_22175.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_22175.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_22175.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_22175.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_22175.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_22175.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22167 with
                       | (uu____22180,ty,uu____22182) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22191 =
                                 let uu____22192 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22192.FStar_Syntax_Syntax.n  in
                               match uu____22191 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22195 ->
                                   let uu____22202 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22202
                               | uu____22203 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22206 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22206
                             then
                               let uu____22211 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22213 =
                                 let uu____22215 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22215
                                  in
                               let uu____22216 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22211 uu____22213 uu____22216
                             else ());
                            r1))
                     in
                  let uu____22221 =
                    let uu____22238 = maybe_eta t1  in
                    let uu____22245 = maybe_eta t2  in
                    (uu____22238, uu____22245)  in
                  (match uu____22221 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_22287 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_22287.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_22287.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_22287.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_22287.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_22287.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_22287.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_22287.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_22287.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22308 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22308
                       then
                         let uu____22311 = destruct_flex_t not_abs wl  in
                         (match uu____22311 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22328 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22328.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22328.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22328.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22328.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22328.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22328.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22328.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22328.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22331 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22331 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22354 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22354
                       then
                         let uu____22357 = destruct_flex_t not_abs wl  in
                         (match uu____22357 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22374 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22374.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22374.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22374.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22374.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22374.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22374.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22374.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22374.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22377 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22377 orig))
                   | uu____22380 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22410 =
                    let uu____22415 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22415 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3134_22443 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22443.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22443.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22445 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22445.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22445.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22446,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3134_22461 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22461.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22461.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22463 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22463.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22463.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22464 -> (x1, x2)  in
                  (match uu____22410 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22483 = as_refinement false env t11  in
                       (match uu____22483 with
                        | (x12,phi11) ->
                            let uu____22491 = as_refinement false env t21  in
                            (match uu____22491 with
                             | (x22,phi21) ->
                                 ((let uu____22500 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22500
                                   then
                                     ((let uu____22505 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22507 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22509 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22505
                                         uu____22507 uu____22509);
                                      (let uu____22512 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22514 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22516 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22512
                                         uu____22514 uu____22516))
                                   else ());
                                  (let uu____22521 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22521 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____22592 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22592
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22604 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22617 =
                                            let uu____22620 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22620
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22617
                                            (p_guard base_prob));
                                         (let uu____22639 =
                                            let uu____22642 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22642
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22639
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22661 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22661)
                                          in
                                       let has_uvars =
                                         (let uu____22666 =
                                            let uu____22668 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22668
                                             in
                                          Prims.op_Negation uu____22666) ||
                                           (let uu____22672 =
                                              let uu____22674 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22674
                                               in
                                            Prims.op_Negation uu____22672)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22678 =
                                           let uu____22683 =
                                             let uu____22692 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22692]  in
                                           mk_t_problem wl1 uu____22683 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22678 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22715 =
                                                solve env1
                                                  (let uu___3179_22717 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3179_22717.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3179_22717.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3179_22717.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3179_22717.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3179_22717.tcenv);
                                                     wl_implicits =
                                                       (uu___3179_22717.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22715 with
                                               | Failed (prob,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      ((Prims.op_Negation
                                                          env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                         && has_uvars)
                                                        ||
                                                        (Prims.op_Negation
                                                           wl2.smt_ok)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success
                                                   (uu____22732,defer_to_tac,uu____22734)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22739 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22739
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3195_22748 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3195_22748.attempting);
                                                         wl_deferred =
                                                           (uu___3195_22748.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3195_22748.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3195_22748.defer_ok);
                                                         smt_ok =
                                                           (uu___3195_22748.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3195_22748.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3195_22748.tcenv);
                                                         wl_implicits =
                                                           (uu___3195_22748.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22751 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22751))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22754,FStar_Syntax_Syntax.Tm_uvar uu____22755) ->
                  let uu____22780 = destruct_flex_t t1 wl  in
                  (match uu____22780 with
                   | (f1,wl1) ->
                       let uu____22787 = destruct_flex_t t2 wl1  in
                       (match uu____22787 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22794;
                    FStar_Syntax_Syntax.pos = uu____22795;
                    FStar_Syntax_Syntax.vars = uu____22796;_},uu____22797),FStar_Syntax_Syntax.Tm_uvar
                 uu____22798) ->
                  let uu____22847 = destruct_flex_t t1 wl  in
                  (match uu____22847 with
                   | (f1,wl1) ->
                       let uu____22854 = destruct_flex_t t2 wl1  in
                       (match uu____22854 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22861,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22862;
                    FStar_Syntax_Syntax.pos = uu____22863;
                    FStar_Syntax_Syntax.vars = uu____22864;_},uu____22865))
                  ->
                  let uu____22914 = destruct_flex_t t1 wl  in
                  (match uu____22914 with
                   | (f1,wl1) ->
                       let uu____22921 = destruct_flex_t t2 wl1  in
                       (match uu____22921 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22928;
                    FStar_Syntax_Syntax.pos = uu____22929;
                    FStar_Syntax_Syntax.vars = uu____22930;_},uu____22931),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22932;
                    FStar_Syntax_Syntax.pos = uu____22933;
                    FStar_Syntax_Syntax.vars = uu____22934;_},uu____22935))
                  ->
                  let uu____23008 = destruct_flex_t t1 wl  in
                  (match uu____23008 with
                   | (f1,wl1) ->
                       let uu____23015 = destruct_flex_t t2 wl1  in
                       (match uu____23015 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23022,uu____23023) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23036 = destruct_flex_t t1 wl  in
                  (match uu____23036 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23043;
                    FStar_Syntax_Syntax.pos = uu____23044;
                    FStar_Syntax_Syntax.vars = uu____23045;_},uu____23046),uu____23047)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23084 = destruct_flex_t t1 wl  in
                  (match uu____23084 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23091,FStar_Syntax_Syntax.Tm_uvar uu____23092) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23105,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23106;
                    FStar_Syntax_Syntax.pos = uu____23107;
                    FStar_Syntax_Syntax.vars = uu____23108;_},uu____23109))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23146,FStar_Syntax_Syntax.Tm_arrow uu____23147) ->
                  solve_t' env
                    (let uu___3296_23175 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23175.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23175.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23175.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23175.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23175.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23175.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23175.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23175.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23175.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23176;
                    FStar_Syntax_Syntax.pos = uu____23177;
                    FStar_Syntax_Syntax.vars = uu____23178;_},uu____23179),FStar_Syntax_Syntax.Tm_arrow
                 uu____23180) ->
                  solve_t' env
                    (let uu___3296_23232 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23232.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23232.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23232.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23232.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23232.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23232.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23232.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23232.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23232.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23233,FStar_Syntax_Syntax.Tm_uvar uu____23234) ->
                  let uu____23247 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23247
              | (uu____23248,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23249;
                    FStar_Syntax_Syntax.pos = uu____23250;
                    FStar_Syntax_Syntax.vars = uu____23251;_},uu____23252))
                  ->
                  let uu____23289 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23289
              | (FStar_Syntax_Syntax.Tm_uvar uu____23290,uu____23291) ->
                  let uu____23304 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23304
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23305;
                    FStar_Syntax_Syntax.pos = uu____23306;
                    FStar_Syntax_Syntax.vars = uu____23307;_},uu____23308),uu____23309)
                  ->
                  let uu____23346 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23346
              | (FStar_Syntax_Syntax.Tm_refine uu____23347,uu____23348) ->
                  let t21 =
                    let uu____23356 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23356  in
                  solve_t env
                    (let uu___3331_23382 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3331_23382.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3331_23382.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3331_23382.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3331_23382.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3331_23382.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3331_23382.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3331_23382.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3331_23382.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3331_23382.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23383,FStar_Syntax_Syntax.Tm_refine uu____23384) ->
                  let t11 =
                    let uu____23392 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23392  in
                  solve_t env
                    (let uu___3338_23418 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3338_23418.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3338_23418.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3338_23418.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3338_23418.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3338_23418.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3338_23418.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3338_23418.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3338_23418.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3338_23418.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23500 =
                    let uu____23501 = guard_of_prob env wl problem t1 t2  in
                    match uu____23501 with
                    | (guard,wl1) ->
                        let uu____23508 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23508
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23727 = br1  in
                        (match uu____23727 with
                         | (p1,w1,uu____23756) ->
                             let uu____23773 = br2  in
                             (match uu____23773 with
                              | (p2,w2,uu____23796) ->
                                  let uu____23801 =
                                    let uu____23803 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23803  in
                                  if uu____23801
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23830 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23830 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23867 = br2  in
                                         (match uu____23867 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23900 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23900
                                                 in
                                              let uu____23905 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23936,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23957) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24016 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24016 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23905
                                                (fun uu____24088  ->
                                                   match uu____24088 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24125 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24125
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24146
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24146
                                                              then
                                                                let uu____24151
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24153
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24151
                                                                  uu____24153
                                                              else ());
                                                             (let uu____24159
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24159
                                                                (fun
                                                                   uu____24195
                                                                    ->
                                                                   match uu____24195
                                                                   with
                                                                   | 
                                                                   (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____24324 -> FStar_Pervasives_Native.None  in
                  let uu____24365 = solve_branches wl brs1 brs2  in
                  (match uu____24365 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24391 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24391 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24418 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24418 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24452 =
                                FStar_List.map
                                  (fun uu____24464  ->
                                     match uu____24464 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24452  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24473 =
                              let uu____24474 =
                                let uu____24475 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24475
                                  (let uu___3437_24483 = wl3  in
                                   {
                                     attempting =
                                       (uu___3437_24483.attempting);
                                     wl_deferred =
                                       (uu___3437_24483.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3437_24483.wl_deferred_to_tac);
                                     ctr = (uu___3437_24483.ctr);
                                     defer_ok = (uu___3437_24483.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3437_24483.umax_heuristic_ok);
                                     tcenv = (uu___3437_24483.tcenv);
                                     wl_implicits =
                                       (uu___3437_24483.wl_implicits)
                                   })
                                 in
                              solve env uu____24474  in
                            (match uu____24473 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24489 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24498 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24498 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24501,uu____24502) ->
                  let head1 =
                    let uu____24526 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24526
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24572 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24572
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24618 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24618
                    then
                      let uu____24622 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24624 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24626 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24622 uu____24624 uu____24626
                    else ());
                   (let no_free_uvars t =
                      (let uu____24640 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24640) &&
                        (let uu____24644 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24644)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24663 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24663 = FStar_Syntax_Util.Equal  in
                    let uu____24664 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24664
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24668 = equal t1 t2  in
                         (if uu____24668
                          then
                            let uu____24671 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24671
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24676 =
                            let uu____24683 = equal t1 t2  in
                            if uu____24683
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24696 = mk_eq2 wl env orig t1 t2  in
                               match uu____24696 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24676 with
                          | (guard,wl1) ->
                              let uu____24717 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24717))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24720,uu____24721) ->
                  let head1 =
                    let uu____24729 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24729
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24775 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24775
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24821 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24821
                    then
                      let uu____24825 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24827 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24829 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24825 uu____24827 uu____24829
                    else ());
                   (let no_free_uvars t =
                      (let uu____24843 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24843) &&
                        (let uu____24847 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24847)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24866 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24866 = FStar_Syntax_Util.Equal  in
                    let uu____24867 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24867
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24871 = equal t1 t2  in
                         (if uu____24871
                          then
                            let uu____24874 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24874
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24879 =
                            let uu____24886 = equal t1 t2  in
                            if uu____24886
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24899 = mk_eq2 wl env orig t1 t2  in
                               match uu____24899 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24879 with
                          | (guard,wl1) ->
                              let uu____24920 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24920))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24923,uu____24924) ->
                  let head1 =
                    let uu____24926 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24926
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24972 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24972
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25018 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25018
                    then
                      let uu____25022 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25024 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25026 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25022 uu____25024 uu____25026
                    else ());
                   (let no_free_uvars t =
                      (let uu____25040 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25040) &&
                        (let uu____25044 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25044)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25063 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25063 = FStar_Syntax_Util.Equal  in
                    let uu____25064 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25064
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25068 = equal t1 t2  in
                         (if uu____25068
                          then
                            let uu____25071 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25071
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25076 =
                            let uu____25083 = equal t1 t2  in
                            if uu____25083
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25096 = mk_eq2 wl env orig t1 t2  in
                               match uu____25096 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25076 with
                          | (guard,wl1) ->
                              let uu____25117 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25117))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25120,uu____25121) ->
                  let head1 =
                    let uu____25123 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25123
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25169 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25169
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25215 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25215
                    then
                      let uu____25219 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25221 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25223 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25219 uu____25221 uu____25223
                    else ());
                   (let no_free_uvars t =
                      (let uu____25237 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25237) &&
                        (let uu____25241 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25241)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25260 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25260 = FStar_Syntax_Util.Equal  in
                    let uu____25261 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25261
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25265 = equal t1 t2  in
                         (if uu____25265
                          then
                            let uu____25268 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25268
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25273 =
                            let uu____25280 = equal t1 t2  in
                            if uu____25280
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25293 = mk_eq2 wl env orig t1 t2  in
                               match uu____25293 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25273 with
                          | (guard,wl1) ->
                              let uu____25314 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25314))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25317,uu____25318) ->
                  let head1 =
                    let uu____25320 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25320
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25360 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25360
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25400 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25400
                    then
                      let uu____25404 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25406 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25408 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25404 uu____25406 uu____25408
                    else ());
                   (let no_free_uvars t =
                      (let uu____25422 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25422) &&
                        (let uu____25426 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25426)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25445 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25445 = FStar_Syntax_Util.Equal  in
                    let uu____25446 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25446
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25450 = equal t1 t2  in
                         (if uu____25450
                          then
                            let uu____25453 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25453
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25458 =
                            let uu____25465 = equal t1 t2  in
                            if uu____25465
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25478 = mk_eq2 wl env orig t1 t2  in
                               match uu____25478 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25458 with
                          | (guard,wl1) ->
                              let uu____25499 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25499))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25502,uu____25503) ->
                  let head1 =
                    let uu____25521 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25521
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25561 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25561
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25601 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25601
                    then
                      let uu____25605 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25607 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25609 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25605 uu____25607 uu____25609
                    else ());
                   (let no_free_uvars t =
                      (let uu____25623 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25623) &&
                        (let uu____25627 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25627)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25646 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25646 = FStar_Syntax_Util.Equal  in
                    let uu____25647 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25647
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25651 = equal t1 t2  in
                         (if uu____25651
                          then
                            let uu____25654 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25654
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25659 =
                            let uu____25666 = equal t1 t2  in
                            if uu____25666
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25679 = mk_eq2 wl env orig t1 t2  in
                               match uu____25679 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25659 with
                          | (guard,wl1) ->
                              let uu____25700 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25700))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25703,FStar_Syntax_Syntax.Tm_match uu____25704) ->
                  let head1 =
                    let uu____25728 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25728
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25768 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25768
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25808
                    then
                      let uu____25812 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25814 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25816 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25812 uu____25814 uu____25816
                    else ());
                   (let no_free_uvars t =
                      (let uu____25830 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25830) &&
                        (let uu____25834 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25834)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25853 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25853 = FStar_Syntax_Util.Equal  in
                    let uu____25854 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25854
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25858 = equal t1 t2  in
                         (if uu____25858
                          then
                            let uu____25861 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25861
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25866 =
                            let uu____25873 = equal t1 t2  in
                            if uu____25873
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25886 = mk_eq2 wl env orig t1 t2  in
                               match uu____25886 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25866 with
                          | (guard,wl1) ->
                              let uu____25907 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25907))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25910,FStar_Syntax_Syntax.Tm_uinst uu____25911) ->
                  let head1 =
                    let uu____25919 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25919
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25959 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25959
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25999 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25999
                    then
                      let uu____26003 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26005 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26007 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26003 uu____26005 uu____26007
                    else ());
                   (let no_free_uvars t =
                      (let uu____26021 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26021) &&
                        (let uu____26025 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26025)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26044 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26044 = FStar_Syntax_Util.Equal  in
                    let uu____26045 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26045
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26049 = equal t1 t2  in
                         (if uu____26049
                          then
                            let uu____26052 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26052
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26057 =
                            let uu____26064 = equal t1 t2  in
                            if uu____26064
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26077 = mk_eq2 wl env orig t1 t2  in
                               match uu____26077 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26057 with
                          | (guard,wl1) ->
                              let uu____26098 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26098))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26101,FStar_Syntax_Syntax.Tm_name uu____26102) ->
                  let head1 =
                    let uu____26104 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26104
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26144 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26144
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26184 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26184
                    then
                      let uu____26188 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26190 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26192 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26188 uu____26190 uu____26192
                    else ());
                   (let no_free_uvars t =
                      (let uu____26206 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26206) &&
                        (let uu____26210 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26210)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26229 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26229 = FStar_Syntax_Util.Equal  in
                    let uu____26230 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26230
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26234 = equal t1 t2  in
                         (if uu____26234
                          then
                            let uu____26237 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26237
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26242 =
                            let uu____26249 = equal t1 t2  in
                            if uu____26249
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26262 = mk_eq2 wl env orig t1 t2  in
                               match uu____26262 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26242 with
                          | (guard,wl1) ->
                              let uu____26283 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26283))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26286,FStar_Syntax_Syntax.Tm_constant uu____26287) ->
                  let head1 =
                    let uu____26289 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26289
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26329 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26329
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26369 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26369
                    then
                      let uu____26373 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26375 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26377 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26373 uu____26375 uu____26377
                    else ());
                   (let no_free_uvars t =
                      (let uu____26391 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26391) &&
                        (let uu____26395 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26395)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26414 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26414 = FStar_Syntax_Util.Equal  in
                    let uu____26415 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26415
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26419 = equal t1 t2  in
                         (if uu____26419
                          then
                            let uu____26422 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26422
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26427 =
                            let uu____26434 = equal t1 t2  in
                            if uu____26434
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26447 = mk_eq2 wl env orig t1 t2  in
                               match uu____26447 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26427 with
                          | (guard,wl1) ->
                              let uu____26468 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26468))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26471,FStar_Syntax_Syntax.Tm_fvar uu____26472) ->
                  let head1 =
                    let uu____26474 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26474
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26520 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26520
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26566 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26566
                    then
                      let uu____26570 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26572 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26574 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26570 uu____26572 uu____26574
                    else ());
                   (let no_free_uvars t =
                      (let uu____26588 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26588) &&
                        (let uu____26592 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26592)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26611 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26611 = FStar_Syntax_Util.Equal  in
                    let uu____26612 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26612
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26616 = equal t1 t2  in
                         (if uu____26616
                          then
                            let uu____26619 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26619
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26624 =
                            let uu____26631 = equal t1 t2  in
                            if uu____26631
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26644 = mk_eq2 wl env orig t1 t2  in
                               match uu____26644 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26624 with
                          | (guard,wl1) ->
                              let uu____26665 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26665))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26668,FStar_Syntax_Syntax.Tm_app uu____26669) ->
                  let head1 =
                    let uu____26687 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26687
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26727 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26727
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26767 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26767
                    then
                      let uu____26771 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26773 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26775 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26771 uu____26773 uu____26775
                    else ());
                   (let no_free_uvars t =
                      (let uu____26789 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26789) &&
                        (let uu____26793 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26793)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26812 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26812 = FStar_Syntax_Util.Equal  in
                    let uu____26813 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26813
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26817 = equal t1 t2  in
                         (if uu____26817
                          then
                            let uu____26820 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26820
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26825 =
                            let uu____26832 = equal t1 t2  in
                            if uu____26832
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26845 = mk_eq2 wl env orig t1 t2  in
                               match uu____26845 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26825 with
                          | (guard,wl1) ->
                              let uu____26866 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26866))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26869,FStar_Syntax_Syntax.Tm_let uu____26870) ->
                  let uu____26897 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26897
                  then
                    let uu____26900 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26900
                  else
                    (let uu____26903 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26903 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26906,uu____26907) ->
                  let uu____26921 =
                    let uu____26927 =
                      let uu____26929 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26931 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26933 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26935 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26929 uu____26931 uu____26933 uu____26935
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26927)
                     in
                  FStar_Errors.raise_error uu____26921
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26939,FStar_Syntax_Syntax.Tm_let uu____26940) ->
                  let uu____26954 =
                    let uu____26960 =
                      let uu____26962 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26964 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26966 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26968 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26962 uu____26964 uu____26966 uu____26968
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26960)
                     in
                  FStar_Errors.raise_error uu____26954
                    t1.FStar_Syntax_Syntax.pos
              | uu____26972 ->
                  let uu____26977 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26977 orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____27043 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27043
           then
             let uu____27048 =
               let uu____27050 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27050  in
             let uu____27051 =
               let uu____27053 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27053  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27048 uu____27051
           else ());
          (let uu____27057 =
             let uu____27059 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27059  in
           if uu____27057
           then
             let uu____27062 =
               FStar_Thunk.mk
                 (fun uu____27067  ->
                    let uu____27068 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27070 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27068 uu____27070)
                in
             giveup env uu____27062 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27092 =
                  FStar_Thunk.mk
                    (fun uu____27097  ->
                       let uu____27098 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27100 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27098 uu____27100)
                   in
                giveup env uu____27092 orig)
             else
               (let uu____27105 =
                  FStar_List.fold_left2
                    (fun uu____27126  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27126 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27147 =
                                 let uu____27152 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27153 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27152
                                   FStar_TypeChecker_Common.EQ uu____27153
                                   "effect universes"
                                  in
                               (match uu____27147 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27105 with
                | (univ_sub_probs,wl1) ->
                    let uu____27173 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27173 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27181 =
                           FStar_List.fold_right2
                             (fun uu____27218  ->
                                fun uu____27219  ->
                                  fun uu____27220  ->
                                    match (uu____27218, uu____27219,
                                            uu____27220)
                                    with
                                    | ((a1,uu____27264),(a2,uu____27266),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27299 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27299 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27181 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27326 =
                                  let uu____27329 =
                                    let uu____27332 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27332
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27329
                                   in
                                FStar_List.append univ_sub_probs uu____27326
                                 in
                              let guard =
                                let guard =
                                  let uu____27354 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27354  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3590_27363 = wl3  in
                                {
                                  attempting = (uu___3590_27363.attempting);
                                  wl_deferred = (uu___3590_27363.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3590_27363.wl_deferred_to_tac);
                                  ctr = (uu___3590_27363.ctr);
                                  defer_ok = (uu___3590_27363.defer_ok);
                                  smt_ok = (uu___3590_27363.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3590_27363.umax_heuristic_ok);
                                  tcenv = (uu___3590_27363.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27365 = attempt sub_probs wl5  in
                              solve env uu____27365))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27383 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27383
           then
             let uu____27388 =
               let uu____27390 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27390
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27392 =
               let uu____27394 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27394
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27388 uu____27392
           else ());
          (let uu____27399 =
             let uu____27404 =
               let uu____27409 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27409
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27404
               (fun uu____27426  ->
                  match uu____27426 with
                  | (c,g) ->
                      let uu____27437 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27437, g))
              in
           match uu____27399 with
           | (c12,g_lift) ->
               ((let uu____27441 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27441
                 then
                   let uu____27446 =
                     let uu____27448 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27448
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27450 =
                     let uu____27452 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27452
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27446 uu____27450
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3610_27462 = wl  in
                     {
                       attempting = (uu___3610_27462.attempting);
                       wl_deferred = (uu___3610_27462.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3610_27462.wl_deferred_to_tac);
                       ctr = (uu___3610_27462.ctr);
                       defer_ok = (uu___3610_27462.defer_ok);
                       smt_ok = (uu___3610_27462.smt_ok);
                       umax_heuristic_ok =
                         (uu___3610_27462.umax_heuristic_ok);
                       tcenv = (uu___3610_27462.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27463 =
                     let rec is_uvar1 t =
                       let uu____27477 =
                         let uu____27478 = FStar_Syntax_Subst.compress t  in
                         uu____27478.FStar_Syntax_Syntax.n  in
                       match uu____27477 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27482 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27497) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27503) ->
                           is_uvar1 t1
                       | uu____27528 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27562  ->
                          fun uu____27563  ->
                            fun uu____27564  ->
                              match (uu____27562, uu____27563, uu____27564)
                              with
                              | ((a1,uu____27608),(a2,uu____27610),(is_sub_probs,wl2))
                                  ->
                                  let uu____27643 = is_uvar1 a1  in
                                  if uu____27643
                                  then
                                    ((let uu____27653 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27653
                                      then
                                        let uu____27658 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27660 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27658 uu____27660
                                      else ());
                                     (let uu____27665 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27665 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27463 with
                   | (is_sub_probs,wl2) ->
                       let uu____27693 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27693 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27701 =
                              let uu____27706 =
                                let uu____27707 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27707
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27706
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27701 with
                             | (uu____27714,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27725 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27727 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27725 s uu____27727
                                    in
                                 let uu____27730 =
                                   let uu____27759 =
                                     let uu____27760 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27760.FStar_Syntax_Syntax.n  in
                                   match uu____27759 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27820 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27820 with
                                        | (a::bs1,c3) ->
                                            let uu____27876 =
                                              let uu____27895 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27895
                                                (fun uu____27999  ->
                                                   match uu____27999 with
                                                   | (l1,l2) ->
                                                       let uu____28072 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28072))
                                               in
                                            (match uu____27876 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28177 ->
                                       let uu____28178 =
                                         let uu____28184 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28184)
                                          in
                                       FStar_Errors.raise_error uu____28178 r
                                    in
                                 (match uu____27730 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28260 =
                                        let uu____28267 =
                                          let uu____28268 =
                                            let uu____28269 =
                                              let uu____28276 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28276,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28269
                                             in
                                          [uu____28268]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28267
                                          (fun b  ->
                                             let uu____28292 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28294 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28296 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28292 uu____28294
                                               uu____28296) r
                                         in
                                      (match uu____28260 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28306 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28306
                                             then
                                               let uu____28311 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28320 =
                                                          let uu____28322 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28322
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28320) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28311
                                             else ());
                                            (let wl4 =
                                               let uu___3682_28330 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3682_28330.attempting);
                                                 wl_deferred =
                                                   (uu___3682_28330.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3682_28330.wl_deferred_to_tac);
                                                 ctr = (uu___3682_28330.ctr);
                                                 defer_ok =
                                                   (uu___3682_28330.defer_ok);
                                                 smt_ok =
                                                   (uu___3682_28330.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3682_28330.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3682_28330.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28355 =
                                                        let uu____28362 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28362, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28355) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28379 =
                                               let f_sort_is =
                                                 let uu____28389 =
                                                   let uu____28390 =
                                                     let uu____28393 =
                                                       let uu____28394 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28394.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28393
                                                      in
                                                   uu____28390.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28389 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28405,uu____28406::is)
                                                     ->
                                                     let uu____28448 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28448
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28481 ->
                                                     let uu____28482 =
                                                       let uu____28488 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28488)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28482 r
                                                  in
                                               let uu____28494 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28529  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28529
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28550 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28550
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28494
                                                in
                                             match uu____28379 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28575 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28575
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28576 =
                                                   let g_sort_is =
                                                     let uu____28586 =
                                                       let uu____28587 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28587.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28586 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28592,uu____28593::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28653 ->
                                                         let uu____28654 =
                                                           let uu____28660 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28660)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28654 r
                                                      in
                                                   let uu____28666 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28701  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28701
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28722
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28722
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28666
                                                    in
                                                 (match uu____28576 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28749 =
                                                          let uu____28754 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28755 =
                                                            let uu____28756 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28756
                                                             in
                                                          (uu____28754,
                                                            uu____28755)
                                                           in
                                                        match uu____28749
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28784 =
                                                          let uu____28787 =
                                                            let uu____28790 =
                                                              let uu____28793
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28793
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28790
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28787
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28784
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28817 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28817
                                                           in
                                                        match g_lift.FStar_TypeChecker_Common.guard_f
                                                        with
                                                        | FStar_TypeChecker_Common.Trivial
                                                             -> guard
                                                        | FStar_TypeChecker_Common.NonTrivial
                                                            f ->
                                                            FStar_Syntax_Util.mk_conj
                                                              guard f
                                                         in
                                                      let wl7 =
                                                        let uu____28828 =
                                                          let uu____28831 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28834  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28834)
                                                            uu____28831
                                                           in
                                                        solve_prob orig
                                                          uu____28828 [] wl6
                                                         in
                                                      let uu____28835 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28835))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28858 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28860 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28860]
              | x -> x  in
            let c12 =
              let uu___3748_28863 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3748_28863.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3748_28863.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3748_28863.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3748_28863.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28864 =
              let uu____28869 =
                FStar_All.pipe_right
                  (let uu___3751_28871 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3751_28871.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3751_28871.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3751_28871.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3751_28871.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28869
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28864
              (fun uu____28885  ->
                 match uu____28885 with
                 | (c,g) ->
                     let uu____28892 =
                       let uu____28894 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28894  in
                     if uu____28892
                     then
                       let uu____28897 =
                         let uu____28903 =
                           let uu____28905 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28907 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28905 uu____28907
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28903)
                          in
                       FStar_Errors.raise_error uu____28897 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28913 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28913
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28919 = lift_c1 ()  in
               solve_eq uu____28919 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28928  ->
                         match uu___31_28928 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28933 -> false))
                  in
               let uu____28935 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28965)::uu____28966,(wp2,uu____28968)::uu____28969)
                     -> (wp1, wp2)
                 | uu____29042 ->
                     let uu____29067 =
                       let uu____29073 =
                         let uu____29075 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29077 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29075 uu____29077
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29073)
                        in
                     FStar_Errors.raise_error uu____29067
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28935 with
               | (wpc1,wpc2) ->
                   let uu____29087 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29087
                   then
                     let uu____29090 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29090 wl
                   else
                     (let uu____29094 =
                        let uu____29101 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29101  in
                      match uu____29094 with
                      | (c2_decl,qualifiers) ->
                          let uu____29122 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29122
                          then
                            let c1_repr =
                              let uu____29129 =
                                let uu____29130 =
                                  let uu____29131 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29131  in
                                let uu____29132 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29130 uu____29132
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29129
                               in
                            let c2_repr =
                              let uu____29135 =
                                let uu____29136 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29137 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29136 uu____29137
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29135
                               in
                            let uu____29139 =
                              let uu____29144 =
                                let uu____29146 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29148 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29146
                                  uu____29148
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29144
                               in
                            (match uu____29139 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29154 = attempt [prob] wl2  in
                                 solve env uu____29154)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29174 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29174
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29197 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29197
                                      then
                                        FStar_Util.print_string
                                          "Using trivial wp ... \n"
                                      else ());
                                     (let c1_univ =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c11.FStar_Syntax_Syntax.result_typ
                                         in
                                      let trivial =
                                        let uu____29207 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29207 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29214 =
                                        let uu____29221 =
                                          let uu____29222 =
                                            let uu____29239 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29242 =
                                              let uu____29253 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29253; wpc1_2]  in
                                            (uu____29239, uu____29242)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29222
                                           in
                                        FStar_Syntax_Syntax.mk uu____29221
                                         in
                                      uu____29214
                                        FStar_Pervasives_Native.None r))
                                  else
                                    (let c2_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c21.FStar_Syntax_Syntax.result_typ
                                        in
                                     let stronger =
                                       FStar_All.pipe_right c2_decl
                                         FStar_Syntax_Util.get_stronger_vc_combinator
                                        in
                                     let uu____29302 =
                                       let uu____29309 =
                                         let uu____29310 =
                                           let uu____29327 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29330 =
                                             let uu____29341 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29350 =
                                               let uu____29361 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29361; wpc1_2]  in
                                             uu____29341 :: uu____29350  in
                                           (uu____29327, uu____29330)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29310
                                          in
                                       FStar_Syntax_Syntax.mk uu____29309  in
                                     uu____29302 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29415 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29415
                              then
                                let uu____29420 =
                                  let uu____29422 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29422
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29420
                              else ());
                             (let uu____29426 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29426 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29435 =
                                      let uu____29438 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29441  ->
                                           FStar_Pervasives_Native.Some
                                             _29441) uu____29438
                                       in
                                    solve_prob orig uu____29435 [] wl1  in
                                  let uu____29442 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29442))))
           in
        let uu____29443 = FStar_Util.physical_equality c1 c2  in
        if uu____29443
        then
          let uu____29446 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29446
        else
          ((let uu____29450 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29450
            then
              let uu____29455 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29457 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29455
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29457
            else ());
           (let uu____29462 =
              let uu____29471 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29474 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29471, uu____29474)  in
            match uu____29462 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29492),FStar_Syntax_Syntax.Total
                    (t2,uu____29494)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29511 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29511 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29513,FStar_Syntax_Syntax.Total uu____29514) ->
                     let uu____29531 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29531 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29535),FStar_Syntax_Syntax.Total
                    (t2,uu____29537)) ->
                     let uu____29554 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29554 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29557),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29559)) ->
                     let uu____29576 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29576 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29579),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29581)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29598 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29598 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29601),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29603)) ->
                     let uu____29620 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29620 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29623,FStar_Syntax_Syntax.Comp uu____29624) ->
                     let uu____29633 =
                       let uu___3875_29636 = problem  in
                       let uu____29639 =
                         let uu____29640 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29640
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29636.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29639;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29636.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29636.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29636.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29636.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29636.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29636.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29636.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29636.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29633 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29641,FStar_Syntax_Syntax.Comp uu____29642) ->
                     let uu____29651 =
                       let uu___3875_29654 = problem  in
                       let uu____29657 =
                         let uu____29658 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29658
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29654.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29657;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29654.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29654.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29654.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29654.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29654.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29654.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29654.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29654.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29651 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29659,FStar_Syntax_Syntax.GTotal uu____29660) ->
                     let uu____29669 =
                       let uu___3887_29672 = problem  in
                       let uu____29675 =
                         let uu____29676 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29676
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29672.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29672.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29672.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29675;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29672.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29672.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29672.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29672.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29672.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29672.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29669 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29677,FStar_Syntax_Syntax.Total uu____29678) ->
                     let uu____29687 =
                       let uu___3887_29690 = problem  in
                       let uu____29693 =
                         let uu____29694 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29694
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29690.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29690.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29690.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29693;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29690.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29690.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29690.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29690.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29690.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29690.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29687 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29695,FStar_Syntax_Syntax.Comp uu____29696) ->
                     let uu____29697 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____29697
                     then
                       let uu____29700 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29700 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29707 =
                            let uu____29712 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29712
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29721 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29722 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29721, uu____29722))
                             in
                          match uu____29707 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29730 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29730
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29738 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29738 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29741 =
                                  FStar_Thunk.mk
                                    (fun uu____29746  ->
                                       let uu____29747 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29749 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29747 uu____29749)
                                   in
                                giveup env uu____29741 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29760 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29760 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29810 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29810 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29835 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29866  ->
                match uu____29866 with
                | (u1,u2) ->
                    let uu____29874 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29876 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29874 uu____29876))
         in
      FStar_All.pipe_right uu____29835 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29913,[])) when
          let uu____29940 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29940 -> "{}"
      | uu____29943 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29970 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29970
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30001 =
              FStar_List.map
                (fun uu____30015  ->
                   match uu____30015 with
                   | (msg,x) ->
                       let uu____30026 =
                         let uu____30028 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30028  in
                       Prims.op_Hat msg uu____30026) defs
               in
            FStar_All.pipe_right uu____30001 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30038 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30040 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30042 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30038 uu____30040 uu____30042 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____30099 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30099
                  then
                    let uu____30107 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30109 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30107
                      (rel_to_string rel) uu____30109
                  else "TOP"  in
                let uu____30115 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30115 with
                | (p,wl1) ->
                    (def_check_prob (Prims.op_Hat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv *
              worklist))
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____30175 =
                let uu____30178 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30181  -> FStar_Pervasives_Native.Some _30181)
                  uu____30178
                 in
              FStar_Syntax_Syntax.new_bv uu____30175 t1  in
            let uu____30182 =
              let uu____30187 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30187
               in
            match uu____30182 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____30259 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30259
         then
           let uu____30264 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30264
         else ());
        (let uu____30271 =
           FStar_Util.record_time (fun uu____30278  -> solve env probs)  in
         match uu____30271 with
         | (sol,ms) ->
             ((let uu____30292 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30292
               then
                 let uu____30297 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30297
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30313 =
                     FStar_Util.record_time
                       (fun uu____30320  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30313 with
                    | ((),ms1) ->
                        ((let uu____30333 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30333
                          then
                            let uu____30338 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30338
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30352 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30352
                     then
                       let uu____30359 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30359
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____30387 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30387
            then
              let uu____30392 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30392
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30400 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30400
             then
               let uu____30405 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30405
             else ());
            (let f2 =
               let uu____30411 =
                 let uu____30412 = FStar_Syntax_Util.unmeta f1  in
                 uu____30412.FStar_Syntax_Syntax.n  in
               match uu____30411 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30416 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4006_30417 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4006_30417.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4006_30417.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4006_30417.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4006_30417.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred
        * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
        -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30469 =
              let uu____30470 =
                let uu____30471 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30472  ->
                       FStar_TypeChecker_Common.NonTrivial _30472)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30471;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30470  in
            FStar_All.pipe_left
              (fun _30479  -> FStar_Pervasives_Native.Some _30479)
              uu____30469
  
let with_guard_no_simp :
  'Auu____30489 .
    'Auu____30489 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30538 =
              let uu____30539 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30540  -> FStar_TypeChecker_Common.NonTrivial _30540)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30539;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30538
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____30573 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30573
           then
             let uu____30578 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30580 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30578
               uu____30580
           else ());
          (let uu____30585 =
             let uu____30590 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30590
              in
           match uu____30585 with
           | (prob,wl) ->
               let g =
                 let uu____30598 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30608  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30598  in
               ((let uu____30630 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30630
                 then
                   let uu____30635 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30635
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30656 = try_teq true env t1 t2  in
        match uu____30656 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30661 = FStar_TypeChecker_Env.get_range env  in
              let uu____30662 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30661 uu____30662);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30670 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30670
              then
                let uu____30675 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30677 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30679 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30675
                  uu____30677 uu____30679
              else ());
             g)
  
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30703 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30703
         then
           let uu____30708 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30710 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30708
             uu____30710
         else ());
        (let uu____30715 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30715 with
         | (prob,x,wl) ->
             let g =
               let uu____30730 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30741  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30730  in
             ((let uu____30763 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30763
               then
                 let uu____30768 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30768
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30776 =
                     let uu____30777 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30777 g1  in
                   FStar_Pervasives_Native.Some uu____30776)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30799 = FStar_TypeChecker_Env.get_range env  in
          let uu____30800 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30799 uu____30800
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30829 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30829
         then
           let uu____30834 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30836 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30834 uu____30836
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30847 =
           let uu____30854 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30854 "sub_comp"
            in
         match uu____30847 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30867 =
                 FStar_Util.record_time
                   (fun uu____30879  ->
                      let uu____30880 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30891  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30880)
                  in
               match uu____30867 with
               | (r,ms) ->
                   ((let uu____30923 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30923
                     then
                       let uu____30928 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30930 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30932 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30928 uu____30930
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30932
                     else ());
                    r))))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____30970  ->
        match uu____30970 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31013 =
                 let uu____31019 =
                   let uu____31021 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31023 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31021 uu____31023
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31019)  in
               let uu____31027 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31013 uu____31027)
               in
            let equiv1 v1 v' =
              let uu____31040 =
                let uu____31045 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31046 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31045, uu____31046)  in
              match uu____31040 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31066 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31097 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31097 with
                      | FStar_Syntax_Syntax.U_unif uu____31104 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31133  ->
                                    match uu____31133 with
                                    | (u,v') ->
                                        let uu____31142 = equiv1 v1 v'  in
                                        if uu____31142
                                        then
                                          let uu____31147 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31147 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31168 -> []))
               in
            let uu____31173 =
              let wl =
                let uu___4119_31177 = empty_worklist env  in
                {
                  attempting = (uu___4119_31177.attempting);
                  wl_deferred = (uu___4119_31177.wl_deferred);
                  wl_deferred_to_tac = (uu___4119_31177.wl_deferred_to_tac);
                  ctr = (uu___4119_31177.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4119_31177.smt_ok);
                  umax_heuristic_ok = (uu___4119_31177.umax_heuristic_ok);
                  tcenv = (uu___4119_31177.tcenv);
                  wl_implicits = (uu___4119_31177.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31196  ->
                      match uu____31196 with
                      | (lb,v1) ->
                          let uu____31203 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31203 with
                           | USolved wl1 -> ()
                           | uu____31206 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31217 =
              match uu____31217 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31229) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____31253,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31255,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31266) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31274,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31283 -> false)
               in
            let uu____31289 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31306  ->
                      match uu____31306 with
                      | (u,v1) ->
                          let uu____31314 = check_ineq (u, v1)  in
                          if uu____31314
                          then true
                          else
                            ((let uu____31322 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31322
                              then
                                let uu____31327 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31329 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31327
                                  uu____31329
                              else ());
                             false)))
               in
            if uu____31289
            then ()
            else
              ((let uu____31339 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31339
                then
                  ((let uu____31345 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31345);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31357 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31357))
                else ());
               (let uu____31370 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31370))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____31445 =
          match uu____31445 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4196_31472 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4196_31472.attempting);
            wl_deferred = (uu___4196_31472.wl_deferred);
            wl_deferred_to_tac = (uu___4196_31472.wl_deferred_to_tac);
            ctr = (uu___4196_31472.ctr);
            defer_ok;
            smt_ok = (uu___4196_31472.smt_ok);
            umax_heuristic_ok = (uu___4196_31472.umax_heuristic_ok);
            tcenv = (uu___4196_31472.tcenv);
            wl_implicits = (uu___4196_31472.wl_implicits)
          }  in
        (let uu____31475 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31475
         then
           let uu____31480 = FStar_Util.string_of_bool defer_ok  in
           let uu____31482 = wl_to_string wl  in
           let uu____31484 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31480 uu____31482 uu____31484
         else ());
        (let g1 =
           let uu____31490 = solve_and_commit env wl fail1  in
           match uu____31490 with
           | FStar_Pervasives_Native.Some
               (uu____31499::uu____31500,uu____31501,uu____31502) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4213_31536 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4213_31536.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4213_31536.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31542 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4218_31553 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4218_31553.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4218_31553.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4218_31553.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4218_31553.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          (let uu____31629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31629
           then
             let uu____31634 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31634
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4232_31641 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4232_31641.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4232_31641.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4232_31641.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4232_31641.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31642 =
             let uu____31644 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31644  in
           if uu____31642
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31656 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31657 =
                        let uu____31659 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31659
                         in
                      FStar_Errors.diag uu____31656 uu____31657)
                   else ();
                   (let vc1 =
                      let uu____31665 =
                        let uu____31669 =
                          let uu____31671 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31671  in
                        FStar_Pervasives_Native.Some uu____31669  in
                      FStar_Profiling.profile
                        (fun uu____31674  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31665 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31678 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31679 =
                         let uu____31681 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31681
                          in
                       FStar_Errors.diag uu____31678 uu____31679)
                    else ();
                    (let uu____31687 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31687 "discharge_guard'" env vc1);
                    (let uu____31689 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31689 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31698 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31699 =
                                 let uu____31701 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31701
                                  in
                               FStar_Errors.diag uu____31698 uu____31699)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31711 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31712 =
                                 let uu____31714 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31714
                                  in
                               FStar_Errors.diag uu____31711 uu____31712)
                            else ();
                            (let vcs =
                               let uu____31728 = FStar_Options.use_tactics ()
                                  in
                               if uu____31728
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31750  ->
                                      (let uu____31752 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31752);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31796  ->
                                               match uu____31796 with
                                               | (env1,goal,opts) ->
                                                   let uu____31812 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31812, opts)))))
                               else
                                 (let uu____31816 =
                                    let uu____31823 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31823)  in
                                  [uu____31816])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31856  ->
                                     match uu____31856 with
                                     | (env1,goal,opts) ->
                                         let uu____31866 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31866 with
                                          | FStar_TypeChecker_Common.Trivial 
                                              ->
                                              if debug1
                                              then
                                                FStar_Util.print_string
                                                  "Goal completely solved by tactic\n"
                                              else ()
                                          | FStar_TypeChecker_Common.NonTrivial
                                              goal1 ->
                                              (FStar_Options.push ();
                                               FStar_Options.set opts;
                                               if debug1
                                               then
                                                 (let uu____31877 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31878 =
                                                    let uu____31880 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31882 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31880 uu____31882
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31877 uu____31878)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31889 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31890 =
                                                    let uu____31892 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31892
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31889 uu____31890)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31910 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31910 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31919 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31919
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31933 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31933 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31963 = try_teq false env t1 t2  in
        match uu____31963 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____32007 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32007 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32014 ->
                     let uu____32015 =
                       let uu____32016 = FStar_Syntax_Subst.compress r  in
                       uu____32016.FStar_Syntax_Syntax.n  in
                     (match uu____32015 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32021) ->
                          unresolved ctx_u'
                      | uu____32038 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32062 = acc  in
            match uu____32062 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32081 = hd1  in
                     (match uu____32081 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32092 = unresolved ctx_u  in
                             if uu____32092
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32103 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32103
                                     then
                                       let uu____32107 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32107
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32116 = teq_nosmt env1 t tm
                                          in
                                       match uu____32116 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4345_32126 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4345_32126.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4348_32128 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4348_32128.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4348_32128.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4348_32128.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32131 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4353_32143 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4353_32143.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4353_32143.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4353_32143.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4353_32143.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4353_32143.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4353_32143.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4353_32143.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4353_32143.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4353_32143.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4353_32143.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4353_32143.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4353_32143.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4353_32143.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4353_32143.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4353_32143.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4353_32143.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4353_32143.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4353_32143.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4353_32143.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4353_32143.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4353_32143.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4353_32143.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4353_32143.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4353_32143.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4353_32143.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4353_32143.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4353_32143.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4353_32143.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4353_32143.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4353_32143.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4353_32143.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4353_32143.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4353_32143.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4353_32143.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4353_32143.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4353_32143.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4353_32143.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4353_32143.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4353_32143.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4353_32143.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4353_32143.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4353_32143.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4358_32148 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4358_32148.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4358_32148.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4358_32148.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4358_32148.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4358_32148.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4358_32148.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4358_32148.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4358_32148.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4358_32148.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4358_32148.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4358_32148.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4358_32148.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4358_32148.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4358_32148.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4358_32148.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4358_32148.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4358_32148.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4358_32148.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4358_32148.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4358_32148.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4358_32148.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4358_32148.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4358_32148.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4358_32148.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4358_32148.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4358_32148.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4358_32148.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4358_32148.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4358_32148.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4358_32148.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4358_32148.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4358_32148.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4358_32148.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4358_32148.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4358_32148.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4358_32148.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4358_32148.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32153 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32153
                                   then
                                     let uu____32158 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32160 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32162 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32164 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32158 uu____32160 uu____32162
                                       reason uu____32164
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4364_32171  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32178 =
                                             let uu____32188 =
                                               let uu____32196 =
                                                 let uu____32198 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32200 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32202 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32198 uu____32200
                                                   uu____32202
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32196, r)
                                                in
                                             [uu____32188]  in
                                           FStar_Errors.add_errors
                                             uu____32178);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32221 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32232  ->
                                               let uu____32233 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32235 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32237 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32233 uu____32235
                                                 reason uu____32237)) env2 g1
                                         true
                                        in
                                     match uu____32221 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4376_32245 = g  in
          let uu____32246 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4376_32245.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4376_32245.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4376_32245.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4376_32245.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32246
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32261 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32261
       then
         let uu____32266 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32266
       else ());
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
type goal_type =
  | FlexRigid of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | FlexFlex of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar)
  
  | Frame of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term) 
  | Imp of FStar_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexRigid _0 -> true | uu____32333 -> false
  
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | FlexRigid _0 -> _0 
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexFlex _0 -> true | uu____32368 -> false
  
let (__proj__FlexFlex__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee  -> match projectee with | FlexFlex _0 -> _0 
let (uu___is_Frame : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Frame _0 -> true | uu____32405 -> false
  
let (__proj__Frame__item___0 :
  goal_type ->
    (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | Frame _0 -> _0 
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp _0 -> true | uu____32442 -> false
  
let (__proj__Imp__item___0 : goal_type -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  -> match projectee with | Imp _0 -> _0 
type goal_dep =
  {
  goal_dep_id: Prims.int ;
  goal_type: goal_type ;
  goal_imp: FStar_TypeChecker_Common.implicit ;
  assignees: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  goal_dep_uvars: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  dependences: goal_dep Prims.list FStar_ST.ref ;
  visited: Prims.int FStar_ST.ref }
let (__proj__Mkgoal_dep__item__goal_dep_id : goal_dep -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_dep_id
  
let (__proj__Mkgoal_dep__item__goal_type : goal_dep -> goal_type) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_type
  
let (__proj__Mkgoal_dep__item__goal_imp :
  goal_dep -> FStar_TypeChecker_Common.implicit) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_imp
  
let (__proj__Mkgoal_dep__item__assignees :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> assignees
  
let (__proj__Mkgoal_dep__item__goal_dep_uvars :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> goal_dep_uvars
  
let (__proj__Mkgoal_dep__item__dependences :
  goal_dep -> goal_dep Prims.list FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> dependences
  
let (__proj__Mkgoal_dep__item__visited : goal_dep -> Prims.int FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; goal_dep_uvars;
        dependences; visited;_} -> visited
  
let (print_uvar_set :
  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set -> Prims.string) =
  fun s  ->
    let uu____32780 =
      let uu____32784 = FStar_Util.set_elements s  in
      FStar_All.pipe_right uu____32784
        (FStar_List.map
           (fun u  ->
              let uu____32796 =
                let uu____32798 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____32798  in
              Prims.op_Hat "?" uu____32796))
       in
    FStar_All.pipe_right uu____32780 (FStar_String.concat "; ")
  
let (print_goal_dep : goal_dep -> Prims.string) =
  fun gd  ->
    let uu____32815 = FStar_Util.string_of_int gd.goal_dep_id  in
    let uu____32817 = print_uvar_set gd.assignees  in
    let uu____32819 =
      let uu____32821 =
        let uu____32825 = FStar_ST.op_Bang gd.dependences  in
        FStar_List.map (fun gd1  -> FStar_Util.string_of_int gd1.goal_dep_id)
          uu____32825
         in
      FStar_All.pipe_right uu____32821 (FStar_String.concat "; ")  in
    let uu____32859 =
      FStar_Syntax_Print.ctx_uvar_to_string
        (gd.goal_imp).FStar_TypeChecker_Common.imp_uvar
       in
    FStar_Util.format4 "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n"
      uu____32815 uu____32817 uu____32819 uu____32859
  
let (sort_goals :
  FStar_TypeChecker_Common.implicits ->
    FStar_TypeChecker_Common.implicits -> FStar_TypeChecker_Common.implicits)
  =
  fun eqs  ->
    fun rest  ->
      let goal_dep_id = FStar_Util.mk_ref Prims.int_zero  in
      let uu____32879 = (Prims.int_zero, Prims.int_one, (Prims.of_int (2)))
         in
      match uu____32879 with
      | (mark_unset,mark_temp,mark_set) ->
          let empty_uv_set = FStar_Syntax_Free.new_uv_set ()  in
          let eq_as_goal_dep eq1 =
            let uu____32911 =
              match ((eq1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ).FStar_Syntax_Syntax.n
              with
              | FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                            fv;
                          FStar_Syntax_Syntax.pos = uu____32933;
                          FStar_Syntax_Syntax.vars = uu____32934;_},uu____32935);
                     FStar_Syntax_Syntax.pos = uu____32936;
                     FStar_Syntax_Syntax.vars = uu____32937;_},uu____32938::
                   (lhs,uu____32940)::(rhs,uu____32942)::[])
                  when
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid
                  ->
                  let flex_lhs = is_flex lhs  in
                  let flex_rhs = is_flex rhs  in
                  if flex_lhs && flex_rhs
                  then
                    let uu____33032 =
                      let uu____33037 = flex_uvar_head lhs  in
                      let uu____33038 = flex_uvar_head rhs  in
                      (uu____33037, uu____33038)  in
                    (match uu____33032 with
                     | (lhs1,rhs1) ->
                         let assignees =
                           let uu____33054 =
                             FStar_Util.set_add lhs1 empty_uv_set  in
                           FStar_Util.set_add rhs1 uu____33054  in
                         ((FlexFlex (lhs1, rhs1)), assignees, assignees))
                  else
                    if flex_lhs
                    then
                      (let lhs1 = flex_uvar_head lhs  in
                       let assignees = FStar_Util.set_add lhs1 empty_uv_set
                          in
                       let dep_uvars = FStar_Syntax_Free.uvars rhs  in
                       ((FlexRigid (lhs1, rhs)), assignees, dep_uvars))
                    else
                      if flex_rhs
                      then
                        (let rhs1 = flex_uvar_head rhs  in
                         let assignees = FStar_Util.set_add rhs1 empty_uv_set
                            in
                         let dep_uvars = FStar_Syntax_Free.uvars lhs  in
                         ((FlexRigid (rhs1, lhs)), assignees, dep_uvars))
                      else
                        failwith
                          "Impossible: deferred goals must be flex on one at least one side"
              | uu____33122 -> failwith "Not an eq"  in
            match uu____32911 with
            | (goal_type,assignees,dep_uvars) ->
                (FStar_Util.incr goal_dep_id;
                 (let uu____33146 = FStar_ST.op_Bang goal_dep_id  in
                  let uu____33169 = FStar_Util.mk_ref []  in
                  let uu____33176 = FStar_Util.mk_ref mark_unset  in
                  {
                    goal_dep_id = uu____33146;
                    goal_type;
                    goal_imp = eq1;
                    assignees;
                    goal_dep_uvars = dep_uvars;
                    dependences = uu____33169;
                    visited = uu____33176
                  }))
             in
          let imp_as_goal_dep i =
            FStar_Util.incr goal_dep_id;
            (let imp_goal uu____33193 =
               (let uu____33195 =
                  FStar_Syntax_Print.term_to_string
                    (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.print1 "Discarding goal as imp: %s\n" uu____33195);
               (let uu____33198 = FStar_ST.op_Bang goal_dep_id  in
                let uu____33221 = FStar_Util.mk_ref []  in
                let uu____33228 = FStar_Util.mk_ref mark_unset  in
                {
                  goal_dep_id = uu____33198;
                  goal_type = (Imp (i.FStar_TypeChecker_Common.imp_uvar));
                  goal_imp = i;
                  assignees = empty_uv_set;
                  goal_dep_uvars = empty_uv_set;
                  dependences = uu____33221;
                  visited = uu____33228
                })
                in
             let uu____33233 =
               FStar_Syntax_Util.un_squash
                 (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                in
             match uu____33233 with
             | FStar_Pervasives_Native.None  -> imp_goal ()
             | FStar_Pervasives_Native.Some t ->
                 let uu____33245 = FStar_Syntax_Util.head_and_args t  in
                 (match uu____33245 with
                  | (head1,args) ->
                      let uu____33288 =
                        let uu____33303 =
                          let uu____33304 = FStar_Syntax_Util.un_uinst head1
                             in
                          uu____33304.FStar_Syntax_Syntax.n  in
                        (uu____33303, args)  in
                      (match uu____33288 with
                       | (FStar_Syntax_Syntax.Tm_fvar
                          fv,(outer,uu____33319)::(inner,uu____33321)::
                          (frame,uu____33323)::[]) when
                           (let uu____33392 =
                              FStar_Ident.lid_of_str
                                "Steel.Memory.Tactics.can_be_split_into"
                               in
                            FStar_Syntax_Syntax.fv_eq_lid fv uu____33392) &&
                             (is_flex frame)
                           ->
                           let imp_uvar = flex_uvar_head frame  in
                           let uu____33395 = FStar_ST.op_Bang goal_dep_id  in
                           let uu____33418 =
                             FStar_Util.set_add imp_uvar empty_uv_set  in
                           let uu____33421 =
                             let uu____33424 = FStar_Syntax_Free.uvars outer
                                in
                             let uu____33427 = FStar_Syntax_Free.uvars inner
                                in
                             FStar_Util.set_union uu____33424 uu____33427  in
                           let uu____33430 = FStar_Util.mk_ref []  in
                           let uu____33437 = FStar_Util.mk_ref mark_unset  in
                           {
                             goal_dep_id = uu____33395;
                             goal_type = (Frame (imp_uvar, outer, inner));
                             goal_imp = i;
                             assignees = uu____33418;
                             goal_dep_uvars = uu____33421;
                             dependences = uu____33430;
                             visited = uu____33437
                           }
                       | uu____33442 -> imp_goal ())))
             in
          let goal_deps =
            let uu____33460 = FStar_List.map eq_as_goal_dep eqs  in
            let uu____33463 = FStar_List.map imp_as_goal_dep rest  in
            FStar_List.append uu____33460 uu____33463  in
          let uu____33466 =
            FStar_List.partition
              (fun gd  ->
                 match gd.goal_type with
                 | Imp uu____33479 -> false
                 | uu____33481 -> true) goal_deps
             in
          (match uu____33466 with
           | (goal_deps1,rest1) ->
               let fill_deps gds =
                 let in_deps deps gd =
                   FStar_Util.for_some
                     (fun d  -> d.goal_dep_id = gd.goal_dep_id) deps
                    in
                 let fill_deps_of_goal gd =
                   let dependent_uvars = gd.goal_dep_uvars  in
                   let current_deps = FStar_ST.op_Bang gd.dependences  in
                   let changed = FStar_Util.mk_ref false  in
                   let deps =
                     FStar_List.filter
                       (fun other_gd  ->
                          let res =
                            if gd.goal_dep_id = other_gd.goal_dep_id
                            then false
                            else
                              (let uu____33580 =
                                 in_deps current_deps other_gd  in
                               if uu____33580
                               then false
                               else
                                 (match other_gd.goal_type with
                                  | FlexFlex uu____33588 ->
                                      let uu____33593 =
                                        FStar_ST.op_Bang other_gd.dependences
                                         in
                                      (match uu____33593 with
                                       | [] -> false
                                       | deps ->
                                           let eligible =
                                             let uu____33626 =
                                               in_deps deps gd  in
                                             Prims.op_Negation uu____33626
                                              in
                                           if eligible
                                           then
                                             let uu____33630 =
                                               let uu____33632 =
                                                 FStar_Util.set_intersect
                                                   dependent_uvars
                                                   other_gd.assignees
                                                  in
                                               FStar_Util.set_is_empty
                                                 uu____33632
                                                in
                                             Prims.op_Negation uu____33630
                                           else false)
                                  | uu____33638 ->
                                      let uu____33639 =
                                        let uu____33641 =
                                          FStar_Util.set_intersect
                                            dependent_uvars
                                            other_gd.assignees
                                           in
                                        FStar_Util.set_is_empty uu____33641
                                         in
                                      Prims.op_Negation uu____33639))
                             in
                          if res
                          then FStar_ST.op_Colon_Equals changed true
                          else ();
                          res) gds
                      in
                   (let uu____33671 = print_goal_dep gd  in
                    let uu____33673 = print_uvar_set dependent_uvars  in
                    let uu____33675 =
                      let uu____33677 =
                        FStar_List.map
                          (fun x  -> FStar_Util.string_of_int x.goal_dep_id)
                          deps
                         in
                      FStar_All.pipe_right uu____33677
                        (FStar_String.concat "; ")
                       in
                    FStar_Util.print3
                      "Deps for goal %s, dep uvars = %s ... [%s]\n"
                      uu____33671 uu____33673 uu____33675);
                   (let uu____33691 =
                      let uu____33694 = FStar_ST.op_Bang gd.dependences  in
                      FStar_List.append deps uu____33694  in
                    FStar_ST.op_Colon_Equals gd.dependences uu____33691);
                   FStar_ST.op_Bang changed  in
                 let rec aux uu____33769 =
                   let changed =
                     FStar_List.fold_right
                       (fun gd  ->
                          fun changed  ->
                            let changed' = fill_deps_of_goal gd  in
                            changed || changed') gds false
                      in
                   if changed then aux () else ()  in
                 aux ()  in
               let topological_sort gds =
                 let out = FStar_Util.mk_ref []  in
                 let rec visit cycle gd =
                   let uu____33819 =
                     let uu____33821 = FStar_ST.op_Bang gd.visited  in
                     uu____33821 = mark_set  in
                   if uu____33819
                   then ()
                   else
                     (let uu____33848 =
                        let uu____33850 = FStar_ST.op_Bang gd.visited  in
                        uu____33850 = mark_temp  in
                      if uu____33848
                      then
                        ((let uu____33876 =
                            let uu____33878 =
                              FStar_List.map print_goal_dep (gd :: cycle)  in
                            FStar_All.pipe_right uu____33878
                              (FStar_String.concat ", ")
                             in
                          FStar_Util.print1 "Cycle:\n%s\n" uu____33876);
                         failwith "Cycle")
                      else
                        (FStar_ST.op_Colon_Equals gd.visited mark_temp;
                         (let uu____33915 = FStar_ST.op_Bang gd.dependences
                             in
                          FStar_List.iter (visit (gd :: cycle)) uu____33915);
                         FStar_ST.op_Colon_Equals gd.visited mark_set;
                         (let uu____33963 =
                            let uu____33966 = FStar_ST.op_Bang out  in gd ::
                              uu____33966
                             in
                          FStar_ST.op_Colon_Equals out uu____33963)))
                    in
                 FStar_List.iter (visit []) gds; FStar_ST.op_Bang out  in
               (fill_deps goal_deps1;
                FStar_Util.print_string
                  "<<<<<<<<<<<<Goals before sorting>>>>>>>>>>>>>>>\n";
                FStar_List.iter
                  (fun gd  ->
                     let uu____34046 = print_goal_dep gd  in
                     FStar_Util.print_string uu____34046) goal_deps1;
                (let goal_deps2 =
                   let uu____34051 = topological_sort goal_deps1  in
                   FStar_List.rev uu____34051  in
                 FStar_Util.print_string
                   "<<<<<<<<<<<<Goals after sorting>>>>>>>>>>>>>>>\n";
                 FStar_List.iter
                   (fun gd  ->
                      let uu____34060 = print_goal_dep gd  in
                      FStar_Util.print_string uu____34060) goal_deps2;
                 FStar_List.map (fun gd  -> gd.goal_imp)
                   (FStar_List.append goal_deps2 rest1))))
  
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      (let uu____34076 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____34076
       then
         let uu____34081 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____34081
       else ());
      (let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____34098 ->
             let prob_as_implicit uu____34109 =
               match uu____34109 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4572_34123 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4572_34123.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4572_34123.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4572_34123.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4572_34123.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4572_34123.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4572_34123.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4572_34123.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4572_34123.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4572_34123.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4572_34123.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4572_34123.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4572_34123.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4572_34123.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4572_34123.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4572_34123.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4572_34123.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4572_34123.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4572_34123.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4572_34123.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4572_34123.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4572_34123.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4572_34123.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4572_34123.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4572_34123.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4572_34123.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4572_34123.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4572_34123.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4572_34123.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4572_34123.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4572_34123.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4572_34123.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4572_34123.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4572_34123.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4572_34123.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4572_34123.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4572_34123.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4572_34123.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4572_34123.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4572_34123.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4572_34123.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4572_34123.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4572_34123.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4572_34123.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4572_34123.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4572_34123.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4572_34123.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4572_34123.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4575_34125 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4575_34125.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4575_34125.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4575_34125.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4575_34125.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4575_34125.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4575_34125.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4575_34125.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4575_34125.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4575_34125.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4575_34125.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4575_34125.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4575_34125.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4575_34125.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4575_34125.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4575_34125.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4575_34125.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4575_34125.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4575_34125.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4575_34125.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4575_34125.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4575_34125.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4575_34125.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4575_34125.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4575_34125.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4575_34125.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4575_34125.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4575_34125.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4575_34125.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4575_34125.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4575_34125.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4575_34125.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4575_34125.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4575_34125.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4575_34125.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4575_34125.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4575_34125.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4575_34125.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4575_34125.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4575_34125.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4575_34125.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4575_34125.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4575_34125.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4575_34125.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4575_34125.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4575_34125.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4575_34125.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____34128 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____34128 with
                         | (uu____34135,tlhs,uu____34137) ->
                             let goal_ty =
                               let uu____34139 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____34139 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____34140 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____34140 with
                              | (goal,ctx_uvar,uu____34155) ->
                                  let uu____34168 =
                                    let uu____34169 = FStar_List.hd ctx_uvar
                                       in
                                    FStar_Pervasives_Native.fst uu____34169
                                     in
                                  {
                                    FStar_TypeChecker_Common.imp_reason = "";
                                    FStar_TypeChecker_Common.imp_uvar =
                                      uu____34168;
                                    FStar_TypeChecker_Common.imp_tm = goal;
                                    FStar_TypeChecker_Common.imp_range =
                                      ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                  }))
                    | uu____34179 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let deferred_goals =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____34189 =
               FStar_List.partition
                 (fun imp  ->
                    let uu____34201 =
                      FStar_Syntax_Unionfind.find
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    match uu____34201 with
                    | FStar_Pervasives_Native.None  -> true
                    | uu____34206 -> false)
                 g1.FStar_TypeChecker_Common.implicits
                in
             (match uu____34189 with
              | (more,imps) ->
                  let more1 =
                    FStar_All.pipe_right more
                      (FStar_List.map
                         (fun i  ->
                            match (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_meta
                            with
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Ctx_uvar_meta_attr a) ->
                                let reason =
                                  let uu____34233 =
                                    FStar_Syntax_Print.term_to_string a  in
                                  FStar_Util.format2 "%s::%s" uu____34233
                                    i.FStar_TypeChecker_Common.imp_reason
                                   in
                                let uu___4600_34236 = i  in
                                {
                                  FStar_TypeChecker_Common.imp_reason =
                                    reason;
                                  FStar_TypeChecker_Common.imp_uvar =
                                    (uu___4600_34236.FStar_TypeChecker_Common.imp_uvar);
                                  FStar_TypeChecker_Common.imp_tm =
                                    (uu___4600_34236.FStar_TypeChecker_Common.imp_tm);
                                  FStar_TypeChecker_Common.imp_range =
                                    (uu___4600_34236.FStar_TypeChecker_Common.imp_range)
                                }
                            | uu____34237 -> i))
                     in
                  let deferred_goals1 = sort_goals deferred_goals more1  in
                  let guard =
                    let uu___4605_34242 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4605_34242.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4605_34242.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4605_34242.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    }  in
                  let resolve_tac =
                    let uu____34249 =
                      FStar_TypeChecker_Env.lookup_attr env
                        FStar_Parser_Const.resolve_implicits_attr_string
                       in
                    match uu____34249 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let (uu____34252,lid::[]);
                        FStar_Syntax_Syntax.sigrng = uu____34254;
                        FStar_Syntax_Syntax.sigquals = uu____34255;
                        FStar_Syntax_Syntax.sigmeta = uu____34256;
                        FStar_Syntax_Syntax.sigattrs = uu____34257;
                        FStar_Syntax_Syntax.sigopts = uu____34258;_}::uu____34259
                        ->
                        let qn = FStar_TypeChecker_Env.lookup_qname env lid
                           in
                        let fv =
                          FStar_Syntax_Syntax.lid_as_fv lid
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_zero) FStar_Pervasives_Native.None
                           in
                        let dd =
                          let uu____34274 =
                            FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn
                             in
                          match uu____34274 with
                          | FStar_Pervasives_Native.Some dd -> dd
                          | FStar_Pervasives_Native.None  ->
                              failwith "Expected a dd"
                           in
                        let term =
                          let uu____34280 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Syntax.fv_to_tm uu____34280  in
                        term
                    | uu____34281 -> failwith "Resolve_tac not found"  in
                  let env1 =
                    let uu___4630_34286 = env  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___4630_34286.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___4630_34286.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___4630_34286.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___4630_34286.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___4630_34286.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___4630_34286.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___4630_34286.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___4630_34286.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___4630_34286.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___4630_34286.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___4630_34286.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___4630_34286.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___4630_34286.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___4630_34286.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___4630_34286.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___4630_34286.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___4630_34286.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___4630_34286.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___4630_34286.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___4630_34286.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___4630_34286.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___4630_34286.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___4630_34286.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___4630_34286.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___4630_34286.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___4630_34286.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___4630_34286.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___4630_34286.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___4630_34286.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___4630_34286.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___4630_34286.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___4630_34286.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___4630_34286.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___4630_34286.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___4630_34286.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___4630_34286.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___4630_34286.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___4630_34286.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___4630_34286.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___4630_34286.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___4630_34286.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___4630_34286.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___4630_34286.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___4630_34286.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___4630_34286.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___4630_34286.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___4630_34286.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac = false
                    }  in
                  (env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
                     resolve_tac deferred_goals1;
                   guard))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____34292 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____34292
        then
          let uu____34297 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____34297
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____34303 = discharge_guard env g3  in
            FStar_All.pipe_left (fun a2  -> ()) uu____34303
        | imp::uu____34305 ->
            let uu____34308 =
              let uu____34314 =
                let uu____34316 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____34318 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____34316 uu____34318
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____34314)
               in
            FStar_Errors.raise_error uu____34308
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34338 = teq env t1 t2  in
        force_trivial_guard env uu____34338
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34357 = teq_nosmt env t1 t2  in
        match uu____34357 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4655_34376 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4655_34376.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4655_34376.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4655_34376.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4655_34376.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____34412 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____34412
         then
           let uu____34417 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____34419 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____34417
             uu____34419
         else ());
        (let uu____34424 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____34424 with
         | (prob,x,wl) ->
             let g =
               let uu____34443 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____34454  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____34443  in
             ((let uu____34476 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____34476
               then
                 let uu____34481 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____34483 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____34485 =
                   let uu____34487 = FStar_Util.must g  in
                   guard_to_string env uu____34487  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____34481 uu____34483 uu____34485
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34524 = check_subtyping env t1 t2  in
        match uu____34524 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____34543 =
              let uu____34544 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____34544 g  in
            FStar_Pervasives_Native.Some uu____34543
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34563 = check_subtyping env t1 t2  in
        match uu____34563 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____34582 =
              let uu____34583 =
                let uu____34584 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____34584]  in
              FStar_TypeChecker_Env.close_guard env uu____34583 g  in
            FStar_Pervasives_Native.Some uu____34582
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____34622 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____34622
         then
           let uu____34627 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____34629 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____34627
             uu____34629
         else ());
        (let uu____34634 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____34634 with
         | (prob,x,wl) ->
             let g =
               let uu____34649 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____34660  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____34649  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____34685 =
                      let uu____34686 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____34686]  in
                    FStar_TypeChecker_Env.close_guard env uu____34685 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34727 = subtype_nosmt env t1 t2  in
        match uu____34727 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  