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
    match projectee with | TERM _0 -> true | uu____49 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____84 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
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
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                (FStar_Dyn.dyn * FStar_Syntax_Syntax.term'
                  FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option
                  ->
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
                    let uu____515 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____515;
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
                   (ctx_uvar, t,
                     (let uu___71_547 = wl  in
                      {
                        attempting = (uu___71_547.attempting);
                        wl_deferred = (uu___71_547.wl_deferred);
                        ctr = (uu___71_547.ctr);
                        defer_ok = (uu___71_547.defer_ok);
                        smt_ok = (uu___71_547.smt_ok);
                        umax_heuristic_ok = (uu___71_547.umax_heuristic_ok);
                        tcenv = (uu___71_547.tcenv);
                        wl_implicits = (imp :: (wl.wl_implicits))
                      })))
  
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
            let uu___77_580 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___77_580.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___77_580.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___77_580.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___77_580.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___77_580.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___77_580.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___77_580.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___77_580.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___77_580.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___77_580.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___77_580.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___77_580.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___77_580.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___77_580.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___77_580.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___77_580.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___77_580.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___77_580.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___77_580.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___77_580.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___77_580.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___77_580.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___77_580.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___77_580.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___77_580.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___77_580.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___77_580.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___77_580.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___77_580.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___77_580.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___77_580.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___77_580.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___77_580.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___77_580.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___77_580.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___77_580.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___77_580.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___77_580.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___77_580.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___77_580.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___77_580.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___77_580.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___77_580.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___77_580.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___77_580.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___77_580.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____582 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____582 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____643 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____678 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____708 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____719 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____730 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_748  ->
    match uu___0_748 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____760 = FStar_Syntax_Util.head_and_args t  in
    match uu____760 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____823 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____825 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____840 =
                     let uu____842 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____842  in
                   FStar_Util.format1 "@<%s>" uu____840
                in
             let uu____846 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____823 uu____825 uu____846
         | uu____849 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_861  ->
      match uu___1_861 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____866 =
            let uu____870 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____872 =
              let uu____876 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____878 =
                let uu____882 =
                  let uu____886 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____886]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____882
                 in
              uu____876 :: uu____878  in
            uu____870 :: uu____872  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____866
      | FStar_TypeChecker_Common.CProb p ->
          let uu____897 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____899 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____901 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____897 uu____899
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____901
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_915  ->
      match uu___2_915 with
      | UNIV (u,t) ->
          let x =
            let uu____921 = FStar_Options.hide_uvar_nums ()  in
            if uu____921
            then "?"
            else
              (let uu____928 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____928 FStar_Util.string_of_int)
             in
          let uu____932 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____932
      | TERM (u,t) ->
          let x =
            let uu____939 = FStar_Options.hide_uvar_nums ()  in
            if uu____939
            then "?"
            else
              (let uu____946 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____946 FStar_Util.string_of_int)
             in
          let uu____950 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____950
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____969 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____969 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____990 =
      let uu____994 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____994
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____990 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1013 .
    (FStar_Syntax_Syntax.term * 'Auu____1013) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1032 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1053  ->
              match uu____1053 with
              | (x,uu____1060) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1032 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    {
      attempting = [];
      wl_deferred = [];
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
        (let uu____1100 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1100
         then
           let uu____1105 = FStar_Thunk.force reason  in
           let uu____1108 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1105 uu____1108
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1131 = FStar_Thunk.mk (fun uu____1134  -> reason)  in
        giveup env uu____1131 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1140  ->
    match uu___3_1140 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1146 .
    'Auu____1146 FStar_TypeChecker_Common.problem ->
      'Auu____1146 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___141_1158 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___141_1158.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___141_1158.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___141_1158.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___141_1158.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___141_1158.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___141_1158.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___141_1158.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1166 .
    'Auu____1166 FStar_TypeChecker_Common.problem ->
      'Auu____1166 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1186  ->
    match uu___4_1186 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1192  -> FStar_TypeChecker_Common.TProb _1192)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1198  -> FStar_TypeChecker_Common.CProb _1198)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1204  ->
    match uu___5_1204 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___153_1210 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___153_1210.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___153_1210.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___153_1210.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___153_1210.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___153_1210.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___153_1210.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___153_1210.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___153_1210.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___153_1210.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___157_1218 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___157_1218.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___157_1218.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___157_1218.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___157_1218.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___157_1218.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___157_1218.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___157_1218.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___157_1218.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___157_1218.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1231  ->
      match uu___6_1231 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1238  ->
    match uu___7_1238 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1251  ->
    match uu___8_1251 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1266  ->
    match uu___9_1266 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1281  ->
    match uu___10_1281 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1295  ->
    match uu___11_1295 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1309  ->
    match uu___12_1309 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1321  ->
    match uu___13_1321 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1337 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1337) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1367 =
          let uu____1369 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1369  in
        if uu____1367
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1406)::bs ->
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
          let uu____1453 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1477 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1477]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1453
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1505 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1529 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1529]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1505
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1576 =
          let uu____1578 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1578  in
        if uu____1576
        then ()
        else
          (let uu____1583 =
             let uu____1586 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1586
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1583 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1635 =
          let uu____1637 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1637  in
        if uu____1635
        then ()
        else
          (let uu____1642 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1642)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1662 =
        let uu____1664 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1664  in
      if uu____1662
      then ()
      else
        (let msgf m =
           let uu____1678 =
             let uu____1680 =
               let uu____1682 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1682 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1680  in
           Prims.op_Hat msg uu____1678  in
         (let uu____1687 = msgf "scope"  in
          let uu____1690 = p_scope prob  in
          def_scope_wf uu____1687 (p_loc prob) uu____1690);
         (let uu____1702 = msgf "guard"  in
          def_check_scoped uu____1702 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1709 = msgf "lhs"  in
                def_check_scoped uu____1709 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1712 = msgf "rhs"  in
                def_check_scoped uu____1712 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1719 = msgf "lhs"  in
                def_check_scoped_comp uu____1719 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1722 = msgf "rhs"  in
                def_check_scoped_comp uu____1722 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___250_1743 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___250_1743.wl_deferred);
          ctr = (uu___250_1743.ctr);
          defer_ok = (uu___250_1743.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___250_1743.umax_heuristic_ok);
          tcenv = (uu___250_1743.tcenv);
          wl_implicits = (uu___250_1743.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1751 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1751 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___254_1774 = empty_worklist env  in
      let uu____1775 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1775;
        wl_deferred = (uu___254_1774.wl_deferred);
        ctr = (uu___254_1774.ctr);
        defer_ok = (uu___254_1774.defer_ok);
        smt_ok = (uu___254_1774.smt_ok);
        umax_heuristic_ok = (uu___254_1774.umax_heuristic_ok);
        tcenv = (uu___254_1774.tcenv);
        wl_implicits = (uu___254_1774.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___259_1796 = wl  in
        {
          attempting = (uu___259_1796.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___259_1796.ctr);
          defer_ok = (uu___259_1796.defer_ok);
          smt_ok = (uu___259_1796.smt_ok);
          umax_heuristic_ok = (uu___259_1796.umax_heuristic_ok);
          tcenv = (uu___259_1796.tcenv);
          wl_implicits = (uu___259_1796.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1823 = FStar_Thunk.mkv reason  in defer uu____1823 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___267_1842 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___267_1842.wl_deferred);
         ctr = (uu___267_1842.ctr);
         defer_ok = (uu___267_1842.defer_ok);
         smt_ok = (uu___267_1842.smt_ok);
         umax_heuristic_ok = (uu___267_1842.umax_heuristic_ok);
         tcenv = (uu___267_1842.tcenv);
         wl_implicits = (uu___267_1842.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1856 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1856 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1890 = FStar_Syntax_Util.type_u ()  in
            match uu____1890 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1902 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1902 with
                 | (uu____1920,tt,wl1) ->
                     let uu____1923 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____1923, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1929  ->
    match uu___14_1929 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _1935  -> FStar_TypeChecker_Common.TProb _1935) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _1941  -> FStar_TypeChecker_Common.CProb _1941) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1949 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1949 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____1969  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2011 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2011 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2011 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2011 FStar_TypeChecker_Common.problem *
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
                        let uu____2098 =
                          let uu____2107 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2107]  in
                        FStar_List.append scope uu____2098
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2150 =
                      let uu____2153 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2153  in
                    FStar_List.append uu____2150
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2172 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2172 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2198 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2198;
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
                  (let uu____2272 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2272 with
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
                  (let uu____2360 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2360 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2398 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2398 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2398 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2398 FStar_TypeChecker_Common.problem *
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
                          let uu____2466 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2466]  in
                        let uu____2485 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2485
                     in
                  let uu____2488 =
                    let uu____2495 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___350_2506 = wl  in
                       {
                         attempting = (uu___350_2506.attempting);
                         wl_deferred = (uu___350_2506.wl_deferred);
                         ctr = (uu___350_2506.ctr);
                         defer_ok = (uu___350_2506.defer_ok);
                         smt_ok = (uu___350_2506.smt_ok);
                         umax_heuristic_ok =
                           (uu___350_2506.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___350_2506.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2495
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2488 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2524 =
                              let uu____2529 =
                                let uu____2530 =
                                  let uu____2539 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2539
                                   in
                                [uu____2530]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2529  in
                            uu____2524 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2567 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2567;
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
                let uu____2615 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2615;
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
  'Auu____2630 .
    worklist ->
      'Auu____2630 FStar_TypeChecker_Common.problem ->
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
              let uu____2663 =
                let uu____2666 =
                  let uu____2667 =
                    let uu____2674 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2674)  in
                  FStar_Syntax_Syntax.NT uu____2667  in
                [uu____2666]  in
              FStar_Syntax_Subst.subst uu____2663 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2696 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2696
        then
          let uu____2704 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2707 = prob_to_string env d  in
          let uu____2709 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2716 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2704 uu____2707 uu____2709 uu____2716
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2728 -> failwith "impossible"  in
           let uu____2731 =
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
           match uu____2731 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2774  ->
            match uu___15_2774 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2786 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2790 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2790 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2821  ->
           match uu___16_2821 with
           | UNIV uu____2824 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2831 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2831
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
        (fun uu___17_2859  ->
           match uu___17_2859 with
           | UNIV (u',t) ->
               let uu____2864 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2864
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2871 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2883 =
        let uu____2884 =
          let uu____2885 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2885
           in
        FStar_Syntax_Subst.compress uu____2884  in
      FStar_All.pipe_right uu____2883 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2897 =
        let uu____2898 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2898  in
      FStar_All.pipe_right uu____2897 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2910 =
        let uu____2914 =
          let uu____2916 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2916  in
        FStar_Pervasives_Native.Some uu____2914  in
      FStar_Profiling.profile (fun uu____2919  -> sn' env t) uu____2910
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
          let uu____2944 =
            let uu____2948 =
              let uu____2950 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2950  in
            FStar_Pervasives_Native.Some uu____2948  in
          FStar_Profiling.profile
            (fun uu____2953  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2944
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2961 = FStar_Syntax_Util.head_and_args t  in
    match uu____2961 with
    | (h,uu____2980) ->
        let uu____3005 =
          let uu____3006 = FStar_Syntax_Subst.compress h  in
          uu____3006.FStar_Syntax_Syntax.n  in
        (match uu____3005 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3011 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3024 =
        let uu____3028 =
          let uu____3030 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3030  in
        FStar_Pervasives_Native.Some uu____3028  in
      FStar_Profiling.profile
        (fun uu____3035  ->
           let uu____3036 = should_strongly_reduce t  in
           if uu____3036
           then
             let uu____3039 =
               let uu____3040 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3040  in
             FStar_All.pipe_right uu____3039 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3024 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3051 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3051) ->
        (FStar_Syntax_Syntax.term * 'Auu____3051)
  =
  fun env  ->
    fun t  ->
      let uu____3074 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3074, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3126  ->
              match uu____3126 with
              | (x,imp) ->
                  let uu____3145 =
                    let uu___456_3146 = x  in
                    let uu____3147 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___456_3146.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___456_3146.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3147
                    }  in
                  (uu____3145, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3171 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3171
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3175 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3175
        | uu____3178 -> u2  in
      let uu____3179 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3179
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3196 =
          let uu____3200 =
            let uu____3202 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3202  in
          FStar_Pervasives_Native.Some uu____3200  in
        FStar_Profiling.profile
          (fun uu____3205  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3196 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3327 = norm_refinement env t12  in
                 match uu____3327 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3342;
                     FStar_Syntax_Syntax.vars = uu____3343;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3367 =
                       let uu____3369 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3371 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3369 uu____3371
                        in
                     failwith uu____3367)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3387 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3387
          | FStar_Syntax_Syntax.Tm_uinst uu____3388 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3425 =
                   let uu____3426 = FStar_Syntax_Subst.compress t1'  in
                   uu____3426.FStar_Syntax_Syntax.n  in
                 match uu____3425 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3441 -> aux true t1'
                 | uu____3449 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3464 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3495 =
                   let uu____3496 = FStar_Syntax_Subst.compress t1'  in
                   uu____3496.FStar_Syntax_Syntax.n  in
                 match uu____3495 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3511 -> aux true t1'
                 | uu____3519 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3534 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3581 =
                   let uu____3582 = FStar_Syntax_Subst.compress t1'  in
                   uu____3582.FStar_Syntax_Syntax.n  in
                 match uu____3581 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3597 -> aux true t1'
                 | uu____3605 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3620 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3635 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3650 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3665 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3680 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3709 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3742 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3763 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3790 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3818 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3855 ->
              let uu____3862 =
                let uu____3864 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3866 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3864 uu____3866
                 in
              failwith uu____3862
          | FStar_Syntax_Syntax.Tm_ascribed uu____3881 ->
              let uu____3908 =
                let uu____3910 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3912 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3910 uu____3912
                 in
              failwith uu____3908
          | FStar_Syntax_Syntax.Tm_delayed uu____3927 ->
              let uu____3950 =
                let uu____3952 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3954 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3952 uu____3954
                 in
              failwith uu____3950
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3969 =
                let uu____3971 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3973 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3971 uu____3973
                 in
              failwith uu____3969
           in
        let uu____3988 = whnf env t1  in aux false uu____3988
  
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
      let uu____4033 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4033 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4074 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4074, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4101 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4101 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4161  ->
    match uu____4161 with
    | (t_base,refopt) ->
        let uu____4192 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4192 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4234 =
      let uu____4238 =
        let uu____4241 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4266  ->
                  match uu____4266 with | (uu____4274,uu____4275,x) -> x))
           in
        FStar_List.append wl.attempting uu____4241  in
      FStar_List.map (wl_prob_to_string wl) uu____4238  in
    FStar_All.pipe_right uu____4234 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4296 .
    ('Auu____4296 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4308  ->
    match uu____4308 with
    | (uu____4315,c,args) ->
        let uu____4318 = print_ctx_uvar c  in
        let uu____4320 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4318 uu____4320
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4330 = FStar_Syntax_Util.head_and_args t  in
    match uu____4330 with
    | (head1,_args) ->
        let uu____4374 =
          let uu____4375 = FStar_Syntax_Subst.compress head1  in
          uu____4375.FStar_Syntax_Syntax.n  in
        (match uu____4374 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4379 -> true
         | uu____4393 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4401 = FStar_Syntax_Util.head_and_args t  in
    match uu____4401 with
    | (head1,_args) ->
        let uu____4444 =
          let uu____4445 = FStar_Syntax_Subst.compress head1  in
          uu____4445.FStar_Syntax_Syntax.n  in
        (match uu____4444 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4449) -> u
         | uu____4466 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4491 = FStar_Syntax_Util.head_and_args t  in
      match uu____4491 with
      | (head1,args) ->
          let uu____4538 =
            let uu____4539 = FStar_Syntax_Subst.compress head1  in
            uu____4539.FStar_Syntax_Syntax.n  in
          (match uu____4538 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4547)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4580 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4605  ->
                         match uu___18_4605 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4610 =
                               let uu____4611 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4611.FStar_Syntax_Syntax.n  in
                             (match uu____4610 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4616 -> false)
                         | uu____4618 -> true))
                  in
               (match uu____4580 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4643 =
                        FStar_List.collect
                          (fun uu___19_4655  ->
                             match uu___19_4655 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4659 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4659]
                             | uu____4660 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4643 FStar_List.rev  in
                    let uu____4683 =
                      let uu____4690 =
                        let uu____4699 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4721  ->
                                  match uu___20_4721 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4725 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4725]
                                  | uu____4726 -> []))
                           in
                        FStar_All.pipe_right uu____4699 FStar_List.rev  in
                      let uu____4749 =
                        let uu____4752 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4752  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4690 uu____4749
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4683 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4788  ->
                                match uu____4788 with
                                | (x,i) ->
                                    let uu____4807 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4807, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4838  ->
                                match uu____4838 with
                                | (a,i) ->
                                    let uu____4857 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4857, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4879 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4901 =
          let uu____4924 =
            let uu____4925 = FStar_Syntax_Subst.compress k  in
            uu____4925.FStar_Syntax_Syntax.n  in
          match uu____4924 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5007 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5007)
              else
                (let uu____5042 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5042 with
                 | (ys',t1,uu____5075) ->
                     let uu____5080 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5080))
          | uu____5119 ->
              let uu____5120 =
                let uu____5125 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5125)  in
              ((ys, t), uu____5120)
           in
        match uu____4901 with
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
                 let uu____5220 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5220 c  in
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
               (let uu____5298 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5298
                then
                  let uu____5303 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5305 = print_ctx_uvar uv  in
                  let uu____5307 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5303 uu____5305 uu____5307
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5316 =
                   let uu____5318 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5318  in
                 let uu____5321 =
                   let uu____5324 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5324
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5316 uu____5321 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5357 =
               let uu____5358 =
                 let uu____5360 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5362 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5360 uu____5362
                  in
               failwith uu____5358  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5428  ->
                       match uu____5428 with
                       | (a,i) ->
                           let uu____5449 =
                             let uu____5450 = FStar_Syntax_Subst.compress a
                                in
                             uu____5450.FStar_Syntax_Syntax.n  in
                           (match uu____5449 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5476 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5486 =
                 let uu____5488 = is_flex g  in Prims.op_Negation uu____5488
                  in
               if uu____5486
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5497 = destruct_flex_t g wl  in
                  match uu____5497 with
                  | ((uu____5502,uv1,args),wl1) ->
                      ((let uu____5507 = args_as_binders args  in
                        assign_solution uu____5507 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___709_5509 = wl1  in
              {
                attempting = (uu___709_5509.attempting);
                wl_deferred = (uu___709_5509.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___709_5509.defer_ok);
                smt_ok = (uu___709_5509.smt_ok);
                umax_heuristic_ok = (uu___709_5509.umax_heuristic_ok);
                tcenv = (uu___709_5509.tcenv);
                wl_implicits = (uu___709_5509.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5534 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5534
         then
           let uu____5539 = FStar_Util.string_of_int pid  in
           let uu____5541 =
             let uu____5543 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5543 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5539 uu____5541
         else ());
        commit sol;
        (let uu___717_5557 = wl  in
         {
           attempting = (uu___717_5557.attempting);
           wl_deferred = (uu___717_5557.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___717_5557.defer_ok);
           smt_ok = (uu___717_5557.smt_ok);
           umax_heuristic_ok = (uu___717_5557.umax_heuristic_ok);
           tcenv = (uu___717_5557.tcenv);
           wl_implicits = (uu___717_5557.wl_implicits)
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
          (let uu____5593 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5593
           then
             let uu____5598 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5602 =
               let uu____5604 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5604 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5598 uu____5602
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
        let uu____5639 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5639 FStar_Util.set_elements  in
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
      let uu____5679 = occurs uk t  in
      match uu____5679 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5718 =
                 let uu____5720 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5722 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5720 uu____5722
                  in
               FStar_Pervasives_Native.Some uu____5718)
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
            let uu____5842 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5842 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5893 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5950  ->
             match uu____5950 with
             | (x,uu____5962) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5980 = FStar_List.last bs  in
      match uu____5980 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6004) ->
          let uu____6015 =
            FStar_Util.prefix_until
              (fun uu___21_6030  ->
                 match uu___21_6030 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6033 -> false) g
             in
          (match uu____6015 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6047,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6084 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6084 with
        | (pfx,uu____6094) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6106 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6106 with
             | (uu____6114,src',wl1) ->
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
                 | uu____6228 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6229 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6293  ->
                  fun uu____6294  ->
                    match (uu____6293, uu____6294) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6397 =
                          let uu____6399 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6399
                           in
                        if uu____6397
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6433 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6433
                           then
                             let uu____6450 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6450)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6229 with | (isect,uu____6500) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6536 'Auu____6537 .
    (FStar_Syntax_Syntax.bv * 'Auu____6536) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6537) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6595  ->
              fun uu____6596  ->
                match (uu____6595, uu____6596) with
                | ((a,uu____6615),(b,uu____6617)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6633 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6633) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6664  ->
           match uu____6664 with
           | (y,uu____6671) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6681 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6681) Prims.list ->
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
                   let uu____6843 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6843
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6876 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6928 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____6972 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____6993 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7001  ->
    match uu___22_7001 with
    | MisMatch (d1,d2) ->
        let uu____7013 =
          let uu____7015 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7017 =
            let uu____7019 =
              let uu____7021 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7021 ")"  in
            Prims.op_Hat ") (" uu____7019  in
          Prims.op_Hat uu____7015 uu____7017  in
        Prims.op_Hat "MisMatch (" uu____7013
    | HeadMatch u ->
        let uu____7028 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7028
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7037  ->
    match uu___23_7037 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7054 -> HeadMatch false
  
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
          let uu____7076 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7076 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7087 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7111 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7121 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7148 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7148
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7149 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7150 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7151 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7164 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7178 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7202) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7208,uu____7209) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7251) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7276;
             FStar_Syntax_Syntax.index = uu____7277;
             FStar_Syntax_Syntax.sort = t2;_},uu____7279)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7287 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7288 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7289 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7304 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7311 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7331 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7331
  
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
           { FStar_Syntax_Syntax.blob = uu____7350;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7351;
             FStar_Syntax_Syntax.ltyp = uu____7352;
             FStar_Syntax_Syntax.rng = uu____7353;_},uu____7354)
            ->
            let uu____7365 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7365 t21
        | (uu____7366,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7367;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7368;
             FStar_Syntax_Syntax.ltyp = uu____7369;
             FStar_Syntax_Syntax.rng = uu____7370;_})
            ->
            let uu____7381 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7381
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7393 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7393
            then FullMatch
            else
              (let uu____7398 =
                 let uu____7407 =
                   let uu____7410 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7410  in
                 let uu____7411 =
                   let uu____7414 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7414  in
                 (uu____7407, uu____7411)  in
               MisMatch uu____7398)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7420),FStar_Syntax_Syntax.Tm_uinst (g,uu____7422)) ->
            let uu____7431 = head_matches env f g  in
            FStar_All.pipe_right uu____7431 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7432) -> HeadMatch true
        | (uu____7434,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7438 = FStar_Const.eq_const c d  in
            if uu____7438
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7448),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7450)) ->
            let uu____7483 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7483
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7493),FStar_Syntax_Syntax.Tm_refine (y,uu____7495)) ->
            let uu____7504 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7504 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7506),uu____7507) ->
            let uu____7512 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7512 head_match
        | (uu____7513,FStar_Syntax_Syntax.Tm_refine (x,uu____7515)) ->
            let uu____7520 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7520 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7521,FStar_Syntax_Syntax.Tm_type
           uu____7522) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7524,FStar_Syntax_Syntax.Tm_arrow uu____7525) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7556),FStar_Syntax_Syntax.Tm_app (head',uu____7558))
            ->
            let uu____7607 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7607 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7609),uu____7610) ->
            let uu____7635 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7635 head_match
        | (uu____7636,FStar_Syntax_Syntax.Tm_app (head1,uu____7638)) ->
            let uu____7663 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7663 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7664,FStar_Syntax_Syntax.Tm_let
           uu____7665) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7693,FStar_Syntax_Syntax.Tm_match uu____7694) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7740,FStar_Syntax_Syntax.Tm_abs
           uu____7741) -> HeadMatch true
        | uu____7779 ->
            let uu____7784 =
              let uu____7793 = delta_depth_of_term env t11  in
              let uu____7796 = delta_depth_of_term env t21  in
              (uu____7793, uu____7796)  in
            MisMatch uu____7784
  
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
              let uu____7865 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7865  in
            (let uu____7867 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7867
             then
               let uu____7872 = FStar_Syntax_Print.term_to_string t  in
               let uu____7874 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7872 uu____7874
             else ());
            (let uu____7879 =
               let uu____7880 = FStar_Syntax_Util.un_uinst head1  in
               uu____7880.FStar_Syntax_Syntax.n  in
             match uu____7879 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7886 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7886 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7900 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7900
                        then
                          let uu____7905 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7905
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7910 ->
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
                      let uu____7928 =
                        let uu____7930 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7930 = FStar_Syntax_Util.Equal  in
                      if uu____7928
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7937 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7937
                          then
                            let uu____7942 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____7944 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7942
                              uu____7944
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7949 -> FStar_Pervasives_Native.None)
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
            (let uu____8101 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8101
             then
               let uu____8106 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8108 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8110 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8106
                 uu____8108 uu____8110
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8138 =
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
               match uu____8138 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8186 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8186 with
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
                  uu____8224),uu____8225)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8246 =
                      let uu____8255 = maybe_inline t11  in
                      let uu____8258 = maybe_inline t21  in
                      (uu____8255, uu____8258)  in
                    match uu____8246 with
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
                 (uu____8301,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8302))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8323 =
                      let uu____8332 = maybe_inline t11  in
                      let uu____8335 = maybe_inline t21  in
                      (uu____8332, uu____8335)  in
                    match uu____8323 with
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
             | MisMatch uu____8390 -> fail1 n_delta r t11 t21
             | uu____8399 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8414 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8414
           then
             let uu____8419 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8421 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8423 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8431 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8448 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8448
                    (fun uu____8483  ->
                       match uu____8483 with
                       | (t11,t21) ->
                           let uu____8491 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8493 =
                             let uu____8495 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8495  in
                           Prims.op_Hat uu____8491 uu____8493))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8419 uu____8421 uu____8423 uu____8431
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8512 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8512 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8527  ->
    match uu___24_8527 with
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
      let uu___1206_8576 = p  in
      let uu____8579 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8580 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1206_8576.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8579;
        FStar_TypeChecker_Common.relation =
          (uu___1206_8576.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8580;
        FStar_TypeChecker_Common.element =
          (uu___1206_8576.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1206_8576.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1206_8576.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1206_8576.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1206_8576.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1206_8576.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8595 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8595
            (fun _8600  -> FStar_TypeChecker_Common.TProb _8600)
      | FStar_TypeChecker_Common.CProb uu____8601 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8624 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8624 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8632 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8632 with
           | (lh,lhs_args) ->
               let uu____8679 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8679 with
                | (rh,rhs_args) ->
                    let uu____8726 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8739,FStar_Syntax_Syntax.Tm_uvar uu____8740)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8829 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8856,uu____8857)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8872,FStar_Syntax_Syntax.Tm_uvar uu____8873)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8888,FStar_Syntax_Syntax.Tm_arrow uu____8889)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8919 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8919.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8919.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8919.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8919.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8919.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8919.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8919.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8919.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8919.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8922,FStar_Syntax_Syntax.Tm_type uu____8923)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8939 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8939.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8939.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8939.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8939.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8939.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8939.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8939.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8939.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8939.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____8942,FStar_Syntax_Syntax.Tm_uvar uu____8943)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1257_8959 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1257_8959.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1257_8959.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1257_8959.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1257_8959.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1257_8959.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1257_8959.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1257_8959.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1257_8959.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1257_8959.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8962,FStar_Syntax_Syntax.Tm_uvar uu____8963)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8978,uu____8979)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8994,FStar_Syntax_Syntax.Tm_uvar uu____8995)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9010,uu____9011) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8726 with
                     | (rank,tp1) ->
                         let uu____9024 =
                           FStar_All.pipe_right
                             (let uu___1277_9028 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1277_9028.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1277_9028.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1277_9028.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1277_9028.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1277_9028.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1277_9028.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1277_9028.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1277_9028.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1277_9028.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9031  ->
                                FStar_TypeChecker_Common.TProb _9031)
                            in
                         (rank, uu____9024))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9035 =
            FStar_All.pipe_right
              (let uu___1281_9039 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1281_9039.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1281_9039.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1281_9039.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1281_9039.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1281_9039.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1281_9039.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1281_9039.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1281_9039.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1281_9039.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9042  -> FStar_TypeChecker_Common.CProb _9042)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9035)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9102 probs =
      match uu____9102 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9183 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9204 = rank wl.tcenv hd1  in
               (match uu____9204 with
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
                      (let uu____9265 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9270 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9270)
                          in
                       if uu____9265
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
          let uu____9343 = FStar_Syntax_Util.head_and_args t  in
          match uu____9343 with
          | (hd1,uu____9362) ->
              let uu____9387 =
                let uu____9388 = FStar_Syntax_Subst.compress hd1  in
                uu____9388.FStar_Syntax_Syntax.n  in
              (match uu____9387 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9393) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9428  ->
                           match uu____9428 with
                           | (y,uu____9437) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9460  ->
                                       match uu____9460 with
                                       | (x,uu____9469) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9474 -> false)
           in
        let uu____9476 = rank tcenv p  in
        match uu____9476 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9485 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9540 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9559 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9578 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9595 = FStar_Thunk.mkv s  in UFailed uu____9595 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9610 = FStar_Thunk.mk s  in UFailed uu____9610 
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
                        let uu____9662 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9662 with
                        | (k,uu____9670) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9683 -> false)))
            | uu____9685 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9737 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9745 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9745 = Prims.int_zero))
                           in
                        if uu____9737 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9766 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9774 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9774 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9766)
               in
            let uu____9778 = filter1 u12  in
            let uu____9781 = filter1 u22  in (uu____9778, uu____9781)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9816 = filter_out_common_univs us1 us2  in
                   (match uu____9816 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9876 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9876 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9879 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9896  ->
                               let uu____9897 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9899 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9897 uu____9899))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9925 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9925 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9951 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9951 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____9954 ->
                   ufailed_thunk
                     (fun uu____9965  ->
                        let uu____9966 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____9968 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9966 uu____9968 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9971,uu____9972) ->
              let uu____9974 =
                let uu____9976 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9978 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9976 uu____9978
                 in
              failwith uu____9974
          | (FStar_Syntax_Syntax.U_unknown ,uu____9981) ->
              let uu____9982 =
                let uu____9984 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9986 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9984 uu____9986
                 in
              failwith uu____9982
          | (uu____9989,FStar_Syntax_Syntax.U_bvar uu____9990) ->
              let uu____9992 =
                let uu____9994 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____9996 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9994 uu____9996
                 in
              failwith uu____9992
          | (uu____9999,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10000 =
                let uu____10002 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10004 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10002 uu____10004
                 in
              failwith uu____10000
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10034 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10034
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10051 = occurs_univ v1 u3  in
              if uu____10051
              then
                let uu____10054 =
                  let uu____10056 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10058 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10056 uu____10058
                   in
                try_umax_components u11 u21 uu____10054
              else
                (let uu____10063 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10063)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10075 = occurs_univ v1 u3  in
              if uu____10075
              then
                let uu____10078 =
                  let uu____10080 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10082 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10080 uu____10082
                   in
                try_umax_components u11 u21 uu____10078
              else
                (let uu____10087 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10087)
          | (FStar_Syntax_Syntax.U_max uu____10088,uu____10089) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10097 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10097
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10103,FStar_Syntax_Syntax.U_max uu____10104) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10112 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10112
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10118,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10120,FStar_Syntax_Syntax.U_name uu____10121) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10123) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10125) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10127,FStar_Syntax_Syntax.U_succ uu____10128) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10130,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10237 = bc1  in
      match uu____10237 with
      | (bs1,mk_cod1) ->
          let uu____10281 = bc2  in
          (match uu____10281 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10392 = aux xs ys  in
                     (match uu____10392 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10475 =
                       let uu____10482 = mk_cod1 xs  in ([], uu____10482)  in
                     let uu____10485 =
                       let uu____10492 = mk_cod2 ys  in ([], uu____10492)  in
                     (uu____10475, uu____10485)
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
                  let uu____10561 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10561 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10564 =
                    let uu____10565 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10565 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10564
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10570 = has_type_guard t1 t2  in (uu____10570, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10571 = has_type_guard t2 t1  in (uu____10571, wl)
  
let is_flex_pat :
  'Auu____10581 'Auu____10582 'Auu____10583 .
    ('Auu____10581 * 'Auu____10582 * 'Auu____10583 Prims.list) -> Prims.bool
  =
  fun uu___25_10597  ->
    match uu___25_10597 with
    | (uu____10606,uu____10607,[]) -> true
    | uu____10611 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10644 = f  in
      match uu____10644 with
      | (uu____10651,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10652;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10653;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10656;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10657;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10658;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10659;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10729  ->
                 match uu____10729 with
                 | (y,uu____10738) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10892 =
                  let uu____10907 =
                    let uu____10910 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10910  in
                  ((FStar_List.rev pat_binders), uu____10907)  in
                FStar_Pervasives_Native.Some uu____10892
            | (uu____10943,[]) ->
                let uu____10974 =
                  let uu____10989 =
                    let uu____10992 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10992  in
                  ((FStar_List.rev pat_binders), uu____10989)  in
                FStar_Pervasives_Native.Some uu____10974
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11083 =
                  let uu____11084 = FStar_Syntax_Subst.compress a  in
                  uu____11084.FStar_Syntax_Syntax.n  in
                (match uu____11083 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11104 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11104
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1609_11134 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1609_11134.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1609_11134.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11138 =
                            let uu____11139 =
                              let uu____11146 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11146)  in
                            FStar_Syntax_Syntax.NT uu____11139  in
                          [uu____11138]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1615_11162 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1615_11162.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1615_11162.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11163 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11203 =
                  let uu____11218 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11218  in
                (match uu____11203 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11293 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11326 ->
               let uu____11327 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11327 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11647 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11647
       then
         let uu____11652 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11652
       else ());
      (let uu____11657 = next_prob probs  in
       match uu____11657 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1640_11684 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1640_11684.wl_deferred);
               ctr = (uu___1640_11684.ctr);
               defer_ok = (uu___1640_11684.defer_ok);
               smt_ok = (uu___1640_11684.smt_ok);
               umax_heuristic_ok = (uu___1640_11684.umax_heuristic_ok);
               tcenv = (uu___1640_11684.tcenv);
               wl_implicits = (uu___1640_11684.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11693 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11693
                 then
                   let uu____11696 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11696
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
                       (let uu____11703 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11703)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1652_11709 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1652_11709.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1652_11709.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1652_11709.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1652_11709.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1652_11709.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1652_11709.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1652_11709.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1652_11709.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1652_11709.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11734 ->
                let uu____11744 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11809  ->
                          match uu____11809 with
                          | (c,uu____11819,uu____11820) -> c < probs.ctr))
                   in
                (match uu____11744 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11868 =
                            let uu____11873 =
                              FStar_List.map
                                (fun uu____11894  ->
                                   match uu____11894 with
                                   | (uu____11910,x,y) ->
                                       let uu____11921 = FStar_Thunk.force x
                                          in
                                       (uu____11921, y)) probs.wl_deferred
                               in
                            (uu____11873, (probs.wl_implicits))  in
                          Success uu____11868
                      | uu____11925 ->
                          let uu____11935 =
                            let uu___1670_11936 = probs  in
                            let uu____11937 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11958  ->
                                      match uu____11958 with
                                      | (uu____11966,uu____11967,y) -> y))
                               in
                            {
                              attempting = uu____11937;
                              wl_deferred = rest;
                              ctr = (uu___1670_11936.ctr);
                              defer_ok = (uu___1670_11936.defer_ok);
                              smt_ok = (uu___1670_11936.smt_ok);
                              umax_heuristic_ok =
                                (uu___1670_11936.umax_heuristic_ok);
                              tcenv = (uu___1670_11936.tcenv);
                              wl_implicits = (uu___1670_11936.wl_implicits)
                            }  in
                          solve env uu____11935))))

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
            let uu____11976 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____11976 with
            | USolved wl1 ->
                let uu____11978 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____11978
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11981 = defer_lit "" orig wl1  in
                solve env uu____11981

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
                  let uu____12032 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12032 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12035 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12048;
                  FStar_Syntax_Syntax.vars = uu____12049;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12052;
                  FStar_Syntax_Syntax.vars = uu____12053;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12066,uu____12067) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12075,FStar_Syntax_Syntax.Tm_uinst uu____12076) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12084 -> USolved wl

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
            ((let uu____12095 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12095
              then
                let uu____12100 = prob_to_string env orig  in
                let uu____12102 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12100 uu____12102
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

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
               let uu____12195 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12195 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12250 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12250
                then
                  let uu____12255 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12257 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12255 uu____12257
                else ());
               (let uu____12262 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12262 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12308 = eq_prob t1 t2 wl2  in
                         (match uu____12308 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12329 ->
                         let uu____12338 = eq_prob t1 t2 wl2  in
                         (match uu____12338 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12388 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12403 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12404 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12403, uu____12404)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12409 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12410 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12409, uu____12410)
                            in
                         (match uu____12388 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12441 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12441 with
                                | (t1_hd,t1_args) ->
                                    let uu____12486 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12486 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12552 =
                                              let uu____12559 =
                                                let uu____12570 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12570 :: t1_args  in
                                              let uu____12587 =
                                                let uu____12596 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12596 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12645  ->
                                                   fun uu____12646  ->
                                                     fun uu____12647  ->
                                                       match (uu____12645,
                                                               uu____12646,
                                                               uu____12647)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12697),
                                                          (a2,uu____12699))
                                                           ->
                                                           let uu____12736 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12736
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12559
                                                uu____12587
                                               in
                                            match uu____12552 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1824_12762 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1824_12762.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1824_12762.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1824_12762.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12773 =
                                                  solve env1 wl'  in
                                                (match uu____12773 with
                                                 | Success (uu____12776,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1833_12780
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1833_12780.attempting);
                                                            wl_deferred =
                                                              (uu___1833_12780.wl_deferred);
                                                            ctr =
                                                              (uu___1833_12780.ctr);
                                                            defer_ok =
                                                              (uu___1833_12780.defer_ok);
                                                            smt_ok =
                                                              (uu___1833_12780.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1833_12780.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1833_12780.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12781 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12813 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12813 with
                                | (t1_base,p1_opt) ->
                                    let uu____12849 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12849 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____12948 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____12948
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
                                               let uu____13001 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13001
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
                                               let uu____13033 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13033
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
                                               let uu____13065 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13065
                                           | uu____13068 -> t_base  in
                                         let uu____13085 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13085 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13099 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13099, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13106 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13106 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13142 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13142 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13178 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13178
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
                              let uu____13202 = combine t11 t21 wl2  in
                              (match uu____13202 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13235 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13235
                                     then
                                       let uu____13240 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13240
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13282 ts1 =
               match uu____13282 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13345 = pairwise out t wl2  in
                        (match uu____13345 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13381 =
               let uu____13392 = FStar_List.hd ts  in (uu____13392, [], wl1)
                in
             let uu____13401 = FStar_List.tl ts  in
             aux uu____13381 uu____13401  in
           let uu____13408 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13408 with
           | (this_flex,this_rigid) ->
               let uu____13434 =
                 let uu____13435 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13435.FStar_Syntax_Syntax.n  in
               (match uu____13434 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13460 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13460
                    then
                      let uu____13463 = destruct_flex_t this_flex wl  in
                      (match uu____13463 with
                       | (flex,wl1) ->
                           let uu____13470 = quasi_pattern env flex  in
                           (match uu____13470 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13489 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13489
                                  then
                                    let uu____13494 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13494
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13501 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1935_13504 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1935_13504.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1935_13504.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1935_13504.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1935_13504.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1935_13504.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1935_13504.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1935_13504.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1935_13504.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1935_13504.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13501)
                | uu____13505 ->
                    ((let uu____13507 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13507
                      then
                        let uu____13512 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13512
                      else ());
                     (let uu____13517 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13517 with
                      | (u,_args) ->
                          let uu____13560 =
                            let uu____13561 = FStar_Syntax_Subst.compress u
                               in
                            uu____13561.FStar_Syntax_Syntax.n  in
                          (match uu____13560 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13589 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13589 with
                                 | (u',uu____13608) ->
                                     let uu____13633 =
                                       let uu____13634 = whnf env u'  in
                                       uu____13634.FStar_Syntax_Syntax.n  in
                                     (match uu____13633 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13656 -> false)
                                  in
                               let uu____13658 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13681  ->
                                         match uu___26_13681 with
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
                                              | uu____13695 -> false)
                                         | uu____13699 -> false))
                                  in
                               (match uu____13658 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13714 = whnf env this_rigid
                                         in
                                      let uu____13715 =
                                        FStar_List.collect
                                          (fun uu___27_13721  ->
                                             match uu___27_13721 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13727 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13727]
                                             | uu____13731 -> [])
                                          bounds_probs
                                         in
                                      uu____13714 :: uu____13715  in
                                    let uu____13732 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13732 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13765 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13780 =
                                               let uu____13781 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13781.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13780 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13793 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13793)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13804 -> bound  in
                                           let uu____13805 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13805)  in
                                         (match uu____13765 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13840 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13840
                                                then
                                                  let wl'1 =
                                                    let uu___1995_13846 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___1995_13846.wl_deferred);
                                                      ctr =
                                                        (uu___1995_13846.ctr);
                                                      defer_ok =
                                                        (uu___1995_13846.defer_ok);
                                                      smt_ok =
                                                        (uu___1995_13846.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___1995_13846.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___1995_13846.tcenv);
                                                      wl_implicits =
                                                        (uu___1995_13846.wl_implicits)
                                                    }  in
                                                  let uu____13847 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13847
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13853 =
                                                  solve_t env eq_prob
                                                    (let uu___2000_13855 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2000_13855.wl_deferred);
                                                       ctr =
                                                         (uu___2000_13855.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2000_13855.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2000_13855.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2000_13855.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13853 with
                                                | Success (uu____13857,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2006_13860 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2006_13860.wl_deferred);
                                                        ctr =
                                                          (uu___2006_13860.ctr);
                                                        defer_ok =
                                                          (uu___2006_13860.defer_ok);
                                                        smt_ok =
                                                          (uu___2006_13860.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2006_13860.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2006_13860.tcenv);
                                                        wl_implicits =
                                                          (uu___2006_13860.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2009_13862 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2009_13862.attempting);
                                                        wl_deferred =
                                                          (uu___2009_13862.wl_deferred);
                                                        ctr =
                                                          (uu___2009_13862.ctr);
                                                        defer_ok =
                                                          (uu___2009_13862.defer_ok);
                                                        smt_ok =
                                                          (uu___2009_13862.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2009_13862.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2009_13862.tcenv);
                                                        wl_implicits =
                                                          (FStar_List.append
                                                             wl'.wl_implicits
                                                             imps)
                                                      }  in
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
                                                    let uu____13878 =
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
                                                    ((let uu____13890 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13890
                                                      then
                                                        let uu____13895 =
                                                          let uu____13897 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13897
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13895
                                                      else ());
                                                     (let uu____13910 =
                                                        let uu____13925 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13925)
                                                         in
                                                      match uu____13910 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____13947))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13973 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____13973
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
                                                                  let uu____13993
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____13993))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14018 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14018
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
                                                                    let uu____14038
                                                                    =
                                                                    let uu____14043
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14043
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14038
                                                                    [] wl2
                                                                     in
                                                                  let uu____14049
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14049))))
                                                      | uu____14050 ->
                                                          let uu____14065 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14065 p)))))))
                           | uu____14072 when flip ->
                               let uu____14073 =
                                 let uu____14075 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14077 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14075 uu____14077
                                  in
                               failwith uu____14073
                           | uu____14080 ->
                               let uu____14081 =
                                 let uu____14083 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14085 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14083 uu____14085
                                  in
                               failwith uu____14081)))))

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
                      (fun uu____14121  ->
                         match uu____14121 with
                         | (x,i) ->
                             let uu____14140 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14140, i)) bs_lhs
                     in
                  let uu____14143 = lhs  in
                  match uu____14143 with
                  | (uu____14144,u_lhs,uu____14146) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14243 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14253 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14253, univ)
                             in
                          match uu____14243 with
                          | (k,univ) ->
                              let uu____14260 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14260 with
                               | (uu____14277,u,wl3) ->
                                   let uu____14280 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14280, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14306 =
                              let uu____14319 =
                                let uu____14330 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14330 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14381  ->
                                   fun uu____14382  ->
                                     match (uu____14381, uu____14382) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14483 =
                                           let uu____14490 =
                                             let uu____14493 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14493
                                              in
                                           copy_uvar u_lhs [] uu____14490 wl2
                                            in
                                         (match uu____14483 with
                                          | (uu____14522,t_a,wl3) ->
                                              let uu____14525 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14525 with
                                               | (uu____14544,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14319
                                ([], wl1)
                               in
                            (match uu____14306 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2120_14600 = ct  in
                                   let uu____14601 =
                                     let uu____14604 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14604
                                      in
                                   let uu____14619 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2120_14600.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2120_14600.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14601;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14619;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2120_14600.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2123_14637 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2123_14637.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2123_14637.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14640 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14640 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14702 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14702 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14713 =
                                          let uu____14718 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14718)  in
                                        TERM uu____14713  in
                                      let uu____14719 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14719 with
                                       | (sub_prob,wl3) ->
                                           let uu____14733 =
                                             let uu____14734 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14734
                                              in
                                           solve env uu____14733))
                             | (x,imp)::formals2 ->
                                 let uu____14756 =
                                   let uu____14763 =
                                     let uu____14766 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14766
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14763 wl1
                                    in
                                 (match uu____14756 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14787 =
                                          let uu____14790 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14790
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14787 u_x
                                         in
                                      let uu____14791 =
                                        let uu____14794 =
                                          let uu____14797 =
                                            let uu____14798 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14798, imp)  in
                                          [uu____14797]  in
                                        FStar_List.append bs_terms
                                          uu____14794
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14791 formals2 wl2)
                              in
                           let uu____14825 = occurs_check u_lhs arrow1  in
                           (match uu____14825 with
                            | (uu____14838,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14854 =
                                    FStar_Thunk.mk
                                      (fun uu____14858  ->
                                         let uu____14859 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14859)
                                     in
                                  giveup_or_defer env orig wl uu____14854
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
              (let uu____14892 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14892
               then
                 let uu____14897 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14900 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14897 (rel_to_string (p_rel orig)) uu____14900
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15031 = rhs wl1 scope env1 subst1  in
                     (match uu____15031 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15054 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15054
                            then
                              let uu____15059 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15059
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15137 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15137 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2193_15139 = hd1  in
                       let uu____15140 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2193_15139.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2193_15139.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15140
                       }  in
                     let hd21 =
                       let uu___2196_15144 = hd2  in
                       let uu____15145 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2196_15144.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2196_15144.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15145
                       }  in
                     let uu____15148 =
                       let uu____15153 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15153
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15148 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15176 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15176
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15183 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15183 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15255 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15255
                                  in
                               ((let uu____15273 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15273
                                 then
                                   let uu____15278 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15280 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15278
                                     uu____15280
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15315 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15351 = aux wl [] env [] bs1 bs2  in
               match uu____15351 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15410 = attempt sub_probs wl2  in
                   solve env1 uu____15410)

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
            let uu___2234_15430 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2234_15430.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2234_15430.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15442 = try_solve env wl'  in
          match uu____15442 with
          | Success (uu____15443,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2243_15447 = wl  in
                  {
                    attempting = (uu___2243_15447.attempting);
                    wl_deferred = (uu___2243_15447.wl_deferred);
                    ctr = (uu___2243_15447.ctr);
                    defer_ok = (uu___2243_15447.defer_ok);
                    smt_ok = (uu___2243_15447.smt_ok);
                    umax_heuristic_ok = (uu___2243_15447.umax_heuristic_ok);
                    tcenv = (uu___2243_15447.tcenv);
                    wl_implicits = (FStar_List.append wl.wl_implicits imps)
                  }  in
                solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____15456 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15456 wl)

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
            let binders_as_bv_set bs =
              let uu____15470 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15470 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15504 = lhs1  in
              match uu____15504 with
              | (uu____15507,ctx_u,uu____15509) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15517 ->
                        let uu____15518 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15518 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15567 = quasi_pattern env1 lhs1  in
              match uu____15567 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15601) ->
                  let uu____15606 = lhs1  in
                  (match uu____15606 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15621 = occurs_check ctx_u rhs1  in
                       (match uu____15621 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15672 =
                                let uu____15680 =
                                  let uu____15682 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15682
                                   in
                                FStar_Util.Inl uu____15680  in
                              (uu____15672, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15710 =
                                 let uu____15712 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15712  in
                               if uu____15710
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15739 =
                                    let uu____15747 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15747  in
                                  let uu____15753 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15739, uu____15753)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15797 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15797 with
              | (rhs_hd,args) ->
                  let uu____15840 = FStar_Util.prefix args  in
                  (match uu____15840 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15912 = lhs1  in
                       (match uu____15912 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15916 =
                              let uu____15927 =
                                let uu____15934 =
                                  let uu____15937 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15937
                                   in
                                copy_uvar u_lhs [] uu____15934 wl1  in
                              match uu____15927 with
                              | (uu____15964,t_last_arg,wl2) ->
                                  let uu____15967 =
                                    let uu____15974 =
                                      let uu____15975 =
                                        let uu____15984 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____15984]  in
                                      FStar_List.append bs_lhs uu____15975
                                       in
                                    copy_uvar u_lhs uu____15974 t_res_lhs wl2
                                     in
                                  (match uu____15967 with
                                   | (uu____16019,lhs',wl3) ->
                                       let uu____16022 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16022 with
                                        | (uu____16039,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15916 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16060 =
                                     let uu____16061 =
                                       let uu____16066 =
                                         let uu____16067 =
                                           let uu____16070 =
                                             let uu____16075 =
                                               let uu____16076 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16076]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16075
                                              in
                                           uu____16070
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16067
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16066)  in
                                     TERM uu____16061  in
                                   [uu____16060]  in
                                 let uu____16101 =
                                   let uu____16108 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16108 with
                                   | (p1,wl3) ->
                                       let uu____16128 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16128 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16101 with
                                  | (sub_probs,wl3) ->
                                      let uu____16160 =
                                        let uu____16161 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16161  in
                                      solve env1 uu____16160))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16195 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16195 with
                | (uu____16213,args) ->
                    (match args with | [] -> false | uu____16249 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16268 =
                  let uu____16269 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16269.FStar_Syntax_Syntax.n  in
                match uu____16268 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16273 -> true
                | uu____16289 -> false  in
              let uu____16291 = quasi_pattern env1 lhs1  in
              match uu____16291 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16309  ->
                         let uu____16310 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16310)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16319 = is_app rhs1  in
                  if uu____16319
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16324 = is_arrow rhs1  in
                     if uu____16324
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16336  ->
                               let uu____16337 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16337)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16341 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16341
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16347 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16347
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16352 = lhs  in
                (match uu____16352 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16356 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16356 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16374 =
                              let uu____16378 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16378
                               in
                            FStar_All.pipe_right uu____16374
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16399 = occurs_check ctx_uv rhs1  in
                          (match uu____16399 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16428 =
                                   let uu____16429 =
                                     let uu____16431 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16431
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16429
                                    in
                                 giveup_or_defer env orig wl uu____16428
                               else
                                 (let uu____16439 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16439
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16446 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16446
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16459  ->
                                              let uu____16460 =
                                                names_to_string1 fvs2  in
                                              let uu____16462 =
                                                names_to_string1 fvs1  in
                                              let uu____16464 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16460 uu____16462
                                                uu____16464)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16476 ->
                          if wl.defer_ok
                          then
                            let uu____16480 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16480
                          else
                            (let uu____16485 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16485 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16511 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16511
                             | (FStar_Util.Inl msg,uu____16513) ->
                                 first_order orig env wl lhs rhs)))

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
                  let uu____16531 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16531
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16537 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16537
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16559 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16559
                else
                  (let uu____16564 =
                     let uu____16581 = quasi_pattern env lhs  in
                     let uu____16588 = quasi_pattern env rhs  in
                     (uu____16581, uu____16588)  in
                   match uu____16564 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16631 = lhs  in
                       (match uu____16631 with
                        | ({ FStar_Syntax_Syntax.n = uu____16632;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16634;_},u_lhs,uu____16636)
                            ->
                            let uu____16639 = rhs  in
                            (match uu____16639 with
                             | (uu____16640,u_rhs,uu____16642) ->
                                 let uu____16643 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16643
                                 then
                                   let uu____16650 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16650
                                 else
                                   (let uu____16653 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16653 with
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
                                        let uu____16685 =
                                          let uu____16692 =
                                            let uu____16695 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16695
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16692
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16685 with
                                         | (uu____16707,w,wl1) ->
                                             let w_app =
                                               let uu____16713 =
                                                 let uu____16718 =
                                                   FStar_List.map
                                                     (fun uu____16729  ->
                                                        match uu____16729
                                                        with
                                                        | (z,uu____16737) ->
                                                            let uu____16742 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16742) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16718
                                                  in
                                               uu____16713
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16744 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16744
                                               then
                                                 let uu____16749 =
                                                   let uu____16753 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16755 =
                                                     let uu____16759 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16761 =
                                                       let uu____16765 =
                                                         term_to_string w  in
                                                       let uu____16767 =
                                                         let uu____16771 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16780 =
                                                           let uu____16784 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16793 =
                                                             let uu____16797
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16797]
                                                              in
                                                           uu____16784 ::
                                                             uu____16793
                                                            in
                                                         uu____16771 ::
                                                           uu____16780
                                                          in
                                                       uu____16765 ::
                                                         uu____16767
                                                        in
                                                     uu____16759 ::
                                                       uu____16761
                                                      in
                                                   uu____16753 :: uu____16755
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16749
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16814 =
                                                     let uu____16819 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16819)  in
                                                   TERM uu____16814  in
                                                 let uu____16820 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16820
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16828 =
                                                        let uu____16833 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16833)
                                                         in
                                                      TERM uu____16828  in
                                                    [s1; s2])
                                                  in
                                               let uu____16834 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16834))))))
                   | uu____16835 ->
                       let uu____16852 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16852)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16906 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16906
            then
              let uu____16911 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16913 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16915 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16917 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16911 uu____16913 uu____16915 uu____16917
            else ());
           (let uu____16928 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16928 with
            | (head1,args1) ->
                let uu____16971 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____16971 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17041 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17041 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17046 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17046)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17067 =
                         FStar_Thunk.mk
                           (fun uu____17074  ->
                              let uu____17075 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17077 = args_to_string args1  in
                              let uu____17081 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17083 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17075 uu____17077 uu____17081
                                uu____17083)
                          in
                       giveup env1 uu____17067 orig
                     else
                       (let uu____17090 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17095 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17095 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17090
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2499_17099 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2499_17099.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2499_17099.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2499_17099.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2499_17099.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2499_17099.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2499_17099.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2499_17099.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2499_17099.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17109 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17109
                                    else solve env1 wl2))
                        else
                          (let uu____17114 = base_and_refinement env1 t1  in
                           match uu____17114 with
                           | (base1,refinement1) ->
                               let uu____17139 = base_and_refinement env1 t2
                                  in
                               (match uu____17139 with
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
                                           let uu____17304 =
                                             FStar_List.fold_right
                                               (fun uu____17344  ->
                                                  fun uu____17345  ->
                                                    match (uu____17344,
                                                            uu____17345)
                                                    with
                                                    | (((a1,uu____17397),
                                                        (a2,uu____17399)),
                                                       (probs,wl3)) ->
                                                        let uu____17448 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17448
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17304 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17491 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17491
                                                 then
                                                   let uu____17496 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17496
                                                 else ());
                                                (let uu____17502 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17502
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
                                                    (let uu____17529 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17529 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17545 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17545
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17553 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17553))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17578 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17578 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17594 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17594
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17602 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17602)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17630 =
                                           match uu____17630 with
                                           | (prob,reason) ->
                                               ((let uu____17647 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17647
                                                 then
                                                   let uu____17652 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17654 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17656 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17652 uu____17654
                                                     uu____17656
                                                 else ());
                                                (let uu____17662 =
                                                   let uu____17671 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17674 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17671, uu____17674)
                                                    in
                                                 match uu____17662 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17687 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17687 with
                                                      | (head1',uu____17705)
                                                          ->
                                                          let uu____17730 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17730
                                                           with
                                                           | (head2',uu____17748)
                                                               ->
                                                               let uu____17773
                                                                 =
                                                                 let uu____17778
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17779
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17778,
                                                                   uu____17779)
                                                                  in
                                                               (match uu____17773
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17781
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17781
                                                                    then
                                                                    let uu____17786
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17788
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17790
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17792
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17786
                                                                    uu____17788
                                                                    uu____17790
                                                                    uu____17792
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17797
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2587_17805
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2587_17805.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17807
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17807
                                                                    then
                                                                    let uu____17812
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17812
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17817 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17829 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17829 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17837 =
                                             let uu____17838 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17838.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17837 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17843 -> false  in
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
                                          | uu____17846 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17849 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2607_17885 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2607_17885.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2607_17885.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2607_17885.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2607_17885.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2607_17885.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2607_17885.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2607_17885.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2607_17885.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17961 = destruct_flex_t scrutinee wl1  in
             match uu____17961 with
             | ((_t,uv,_args),wl2) ->
                 let uu____17972 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____17972 with
                  | (xs,pat_term,uu____17988,uu____17989) ->
                      let uu____17994 =
                        FStar_List.fold_left
                          (fun uu____18017  ->
                             fun x  ->
                               match uu____18017 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18038 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18038 with
                                    | (uu____18057,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____17994 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18078 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18078 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2647_18095 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2647_18095.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2647_18095.umax_heuristic_ok);
                                    tcenv = (uu___2647_18095.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18106 = solve env1 wl'  in
                                (match uu____18106 with
                                 | Success (uu____18109,imps) ->
                                     let wl'1 =
                                       let uu___2655_18112 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2655_18112.wl_deferred);
                                         ctr = (uu___2655_18112.ctr);
                                         defer_ok =
                                           (uu___2655_18112.defer_ok);
                                         smt_ok = (uu___2655_18112.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2655_18112.umax_heuristic_ok);
                                         tcenv = (uu___2655_18112.tcenv);
                                         wl_implicits =
                                           (uu___2655_18112.wl_implicits)
                                       }  in
                                     let uu____18113 = solve env1 wl'1  in
                                     (match uu____18113 with
                                      | Success (uu____18116,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2663_18120 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2663_18120.attempting);
                                                 wl_deferred =
                                                   (uu___2663_18120.wl_deferred);
                                                 ctr = (uu___2663_18120.ctr);
                                                 defer_ok =
                                                   (uu___2663_18120.defer_ok);
                                                 smt_ok =
                                                   (uu___2663_18120.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2663_18120.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2663_18120.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18121 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18127 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18150 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18150
                 then
                   let uu____18155 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18157 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18155 uu____18157
                 else ());
                (let uu____18162 =
                   let uu____18183 =
                     let uu____18192 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18192)  in
                   let uu____18199 =
                     let uu____18208 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18208)  in
                   (uu____18183, uu____18199)  in
                 match uu____18162 with
                 | ((uu____18238,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18241;
                                   FStar_Syntax_Syntax.vars = uu____18242;_}),
                    (s,t)) ->
                     let uu____18313 =
                       let uu____18315 = is_flex scrutinee  in
                       Prims.op_Negation uu____18315  in
                     if uu____18313
                     then
                       ((let uu____18326 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18326
                         then
                           let uu____18331 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18331
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18350 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18350
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18365 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18365
                           then
                             let uu____18370 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18372 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18370 uu____18372
                           else ());
                          (let pat_discriminates uu___28_18397 =
                             match uu___28_18397 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18413;
                                  FStar_Syntax_Syntax.p = uu____18414;_},FStar_Pervasives_Native.None
                                ,uu____18415) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18429;
                                  FStar_Syntax_Syntax.p = uu____18430;_},FStar_Pervasives_Native.None
                                ,uu____18431) -> true
                             | uu____18458 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18561 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18561 with
                                       | (uu____18563,uu____18564,t') ->
                                           let uu____18582 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18582 with
                                            | (FullMatch ,uu____18594) ->
                                                true
                                            | (HeadMatch
                                               uu____18608,uu____18609) ->
                                                true
                                            | uu____18624 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18661 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18661
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18672 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18672 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18760,uu____18761) ->
                                       branches1
                                   | uu____18906 -> branches  in
                                 let uu____18961 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____18970 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____18970 with
                                        | (p,uu____18974,uu____18975) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19004  -> FStar_Util.Inr _19004)
                                   uu____18961))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19034 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19034 with
                                | (p,uu____19043,e) ->
                                    ((let uu____19062 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19062
                                      then
                                        let uu____19067 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19069 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19067 uu____19069
                                      else ());
                                     (let uu____19074 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19089  -> FStar_Util.Inr _19089)
                                        uu____19074)))))
                 | ((s,t),(uu____19092,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19095;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19096;_}))
                     ->
                     let uu____19165 =
                       let uu____19167 = is_flex scrutinee  in
                       Prims.op_Negation uu____19167  in
                     if uu____19165
                     then
                       ((let uu____19178 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19178
                         then
                           let uu____19183 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19183
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19202 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19202
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19217 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19217
                           then
                             let uu____19222 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19224 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19222 uu____19224
                           else ());
                          (let pat_discriminates uu___28_19249 =
                             match uu___28_19249 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19265;
                                  FStar_Syntax_Syntax.p = uu____19266;_},FStar_Pervasives_Native.None
                                ,uu____19267) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19281;
                                  FStar_Syntax_Syntax.p = uu____19282;_},FStar_Pervasives_Native.None
                                ,uu____19283) -> true
                             | uu____19310 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19413 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19413 with
                                       | (uu____19415,uu____19416,t') ->
                                           let uu____19434 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19434 with
                                            | (FullMatch ,uu____19446) ->
                                                true
                                            | (HeadMatch
                                               uu____19460,uu____19461) ->
                                                true
                                            | uu____19476 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19513 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19513
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19524 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19524 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19612,uu____19613) ->
                                       branches1
                                   | uu____19758 -> branches  in
                                 let uu____19813 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19822 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19822 with
                                        | (p,uu____19826,uu____19827) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19856  -> FStar_Util.Inr _19856)
                                   uu____19813))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19886 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19886 with
                                | (p,uu____19895,e) ->
                                    ((let uu____19914 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19914
                                      then
                                        let uu____19919 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19921 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19919 uu____19921
                                      else ());
                                     (let uu____19926 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19941  -> FStar_Util.Inr _19941)
                                        uu____19926)))))
                 | uu____19942 ->
                     ((let uu____19964 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____19964
                       then
                         let uu____19969 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____19971 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____19969 uu____19971
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20017 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20017
            then
              let uu____20022 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20024 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20026 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20028 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20022 uu____20024 uu____20026 uu____20028
            else ());
           (let uu____20033 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20033 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20064,uu____20065) ->
                     let rec may_relate head3 =
                       let uu____20093 =
                         let uu____20094 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20094.FStar_Syntax_Syntax.n  in
                       match uu____20093 with
                       | FStar_Syntax_Syntax.Tm_name uu____20098 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20100 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20125 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20125 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20127 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20130
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20131 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20134,uu____20135) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20177) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20183) ->
                           may_relate t
                       | uu____20188 -> false  in
                     let uu____20190 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20190 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20203 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20203
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20213 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20213
                          then
                            let uu____20216 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20216 with
                             | (guard,wl2) ->
                                 let uu____20223 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20223)
                          else
                            (let uu____20226 =
                               FStar_Thunk.mk
                                 (fun uu____20233  ->
                                    let uu____20234 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20236 =
                                      let uu____20238 =
                                        let uu____20242 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20242
                                          (fun x  ->
                                             let uu____20249 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20249)
                                         in
                                      FStar_Util.dflt "" uu____20238  in
                                    let uu____20254 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20256 =
                                      let uu____20258 =
                                        let uu____20262 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20262
                                          (fun x  ->
                                             let uu____20269 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20269)
                                         in
                                      FStar_Util.dflt "" uu____20258  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20234 uu____20236 uu____20254
                                      uu____20256)
                                in
                             giveup env1 uu____20226 orig))
                 | (HeadMatch (true ),uu____20275) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20290 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20290 with
                        | (guard,wl2) ->
                            let uu____20297 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20297)
                     else
                       (let uu____20300 =
                          FStar_Thunk.mk
                            (fun uu____20305  ->
                               let uu____20306 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20308 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20306 uu____20308)
                           in
                        giveup env1 uu____20300 orig)
                 | (uu____20311,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2838_20325 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2838_20325.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2838_20325.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2838_20325.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2838_20325.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2838_20325.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2838_20325.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2838_20325.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2838_20325.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20352 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20352
          then
            let uu____20355 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20355
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20361 =
                let uu____20364 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20364  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20361 t1);
             (let uu____20383 =
                let uu____20386 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20386  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20383 t2);
             (let uu____20405 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20405
              then
                let uu____20409 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20411 =
                  let uu____20413 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20415 =
                    let uu____20417 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20417  in
                  Prims.op_Hat uu____20413 uu____20415  in
                let uu____20420 =
                  let uu____20422 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20424 =
                    let uu____20426 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20426  in
                  Prims.op_Hat uu____20422 uu____20424  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20409 uu____20411 uu____20420
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20433,uu____20434) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20458,FStar_Syntax_Syntax.Tm_delayed uu____20459) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20483,uu____20484) ->
                  let uu____20511 =
                    let uu___2869_20512 = problem  in
                    let uu____20513 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2869_20512.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20513;
                      FStar_TypeChecker_Common.relation =
                        (uu___2869_20512.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2869_20512.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2869_20512.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2869_20512.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2869_20512.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2869_20512.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2869_20512.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2869_20512.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20511 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20514,uu____20515) ->
                  let uu____20522 =
                    let uu___2875_20523 = problem  in
                    let uu____20524 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2875_20523.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20524;
                      FStar_TypeChecker_Common.relation =
                        (uu___2875_20523.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2875_20523.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2875_20523.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2875_20523.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2875_20523.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2875_20523.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2875_20523.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2875_20523.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20522 wl
              | (uu____20525,FStar_Syntax_Syntax.Tm_ascribed uu____20526) ->
                  let uu____20553 =
                    let uu___2881_20554 = problem  in
                    let uu____20555 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2881_20554.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2881_20554.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2881_20554.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20555;
                      FStar_TypeChecker_Common.element =
                        (uu___2881_20554.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2881_20554.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2881_20554.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2881_20554.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2881_20554.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2881_20554.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20553 wl
              | (uu____20556,FStar_Syntax_Syntax.Tm_meta uu____20557) ->
                  let uu____20564 =
                    let uu___2887_20565 = problem  in
                    let uu____20566 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2887_20565.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2887_20565.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2887_20565.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20566;
                      FStar_TypeChecker_Common.element =
                        (uu___2887_20565.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2887_20565.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2887_20565.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2887_20565.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2887_20565.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2887_20565.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20564 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20568),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20570)) ->
                  let uu____20579 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20579
              | (FStar_Syntax_Syntax.Tm_bvar uu____20580,uu____20581) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20583,FStar_Syntax_Syntax.Tm_bvar uu____20584) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20654 =
                    match uu___29_20654 with
                    | [] -> c
                    | bs ->
                        let uu____20682 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20682
                     in
                  let uu____20693 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20693 with
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
                                    let uu____20842 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20842
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
                  let mk_t t l uu___30_20931 =
                    match uu___30_20931 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____20973 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____20973 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21118 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21119 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21118
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21119 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21121,uu____21122) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21153 -> true
                    | uu____21173 -> false  in
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
                      (let uu____21233 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2989_21241 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2989_21241.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2989_21241.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2989_21241.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2989_21241.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2989_21241.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2989_21241.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2989_21241.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2989_21241.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2989_21241.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2989_21241.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2989_21241.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2989_21241.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2989_21241.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2989_21241.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2989_21241.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2989_21241.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2989_21241.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2989_21241.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2989_21241.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2989_21241.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2989_21241.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2989_21241.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2989_21241.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2989_21241.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2989_21241.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2989_21241.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2989_21241.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2989_21241.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2989_21241.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2989_21241.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2989_21241.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2989_21241.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2989_21241.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2989_21241.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2989_21241.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2989_21241.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2989_21241.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2989_21241.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2989_21241.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2989_21241.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2989_21241.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2989_21241.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2989_21241.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2989_21241.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21233 with
                       | (uu____21246,ty,uu____21248) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21257 =
                                 let uu____21258 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21258.FStar_Syntax_Syntax.n  in
                               match uu____21257 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21261 ->
                                   let uu____21268 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21268
                               | uu____21269 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21272 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21272
                             then
                               let uu____21277 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21279 =
                                 let uu____21281 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21281
                                  in
                               let uu____21282 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21277 uu____21279 uu____21282
                             else ());
                            r1))
                     in
                  let uu____21287 =
                    let uu____21304 = maybe_eta t1  in
                    let uu____21311 = maybe_eta t2  in
                    (uu____21304, uu____21311)  in
                  (match uu____21287 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3010_21353 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3010_21353.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3010_21353.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3010_21353.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3010_21353.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3010_21353.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3010_21353.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3010_21353.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3010_21353.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21374 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21374
                       then
                         let uu____21377 = destruct_flex_t not_abs wl  in
                         (match uu____21377 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3027_21394 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3027_21394.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3027_21394.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3027_21394.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3027_21394.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3027_21394.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3027_21394.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3027_21394.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3027_21394.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21397 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21397 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21420 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21420
                       then
                         let uu____21423 = destruct_flex_t not_abs wl  in
                         (match uu____21423 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3027_21440 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3027_21440.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3027_21440.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3027_21440.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3027_21440.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3027_21440.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3027_21440.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3027_21440.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3027_21440.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21443 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21443 orig))
                   | uu____21446 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21464,FStar_Syntax_Syntax.Tm_abs uu____21465) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21496 -> true
                    | uu____21516 -> false  in
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
                      (let uu____21576 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2989_21584 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2989_21584.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2989_21584.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2989_21584.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2989_21584.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2989_21584.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2989_21584.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2989_21584.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2989_21584.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2989_21584.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2989_21584.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2989_21584.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2989_21584.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2989_21584.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2989_21584.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2989_21584.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2989_21584.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2989_21584.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2989_21584.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2989_21584.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2989_21584.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2989_21584.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2989_21584.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2989_21584.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2989_21584.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2989_21584.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2989_21584.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2989_21584.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2989_21584.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2989_21584.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2989_21584.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2989_21584.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2989_21584.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2989_21584.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2989_21584.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2989_21584.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2989_21584.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2989_21584.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2989_21584.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2989_21584.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2989_21584.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2989_21584.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2989_21584.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2989_21584.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2989_21584.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21576 with
                       | (uu____21589,ty,uu____21591) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21600 =
                                 let uu____21601 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21601.FStar_Syntax_Syntax.n  in
                               match uu____21600 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21604 ->
                                   let uu____21611 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21611
                               | uu____21612 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21615 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21615
                             then
                               let uu____21620 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21622 =
                                 let uu____21624 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21624
                                  in
                               let uu____21625 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21620 uu____21622 uu____21625
                             else ());
                            r1))
                     in
                  let uu____21630 =
                    let uu____21647 = maybe_eta t1  in
                    let uu____21654 = maybe_eta t2  in
                    (uu____21647, uu____21654)  in
                  (match uu____21630 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3010_21696 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3010_21696.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3010_21696.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3010_21696.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3010_21696.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3010_21696.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3010_21696.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3010_21696.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3010_21696.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21717 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21717
                       then
                         let uu____21720 = destruct_flex_t not_abs wl  in
                         (match uu____21720 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3027_21737 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3027_21737.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3027_21737.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3027_21737.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3027_21737.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3027_21737.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3027_21737.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3027_21737.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3027_21737.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21740 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21740 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21763 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21763
                       then
                         let uu____21766 = destruct_flex_t not_abs wl  in
                         (match uu____21766 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3027_21783 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3027_21783.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3027_21783.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3027_21783.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3027_21783.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3027_21783.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3027_21783.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3027_21783.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3027_21783.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21786 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21786 orig))
                   | uu____21789 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21819 =
                    let uu____21824 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21824 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3050_21852 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3050_21852.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3050_21852.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3052_21854 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3052_21854.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3052_21854.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21855,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3050_21870 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3050_21870.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3050_21870.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3052_21872 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3052_21872.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3052_21872.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21873 -> (x1, x2)  in
                  (match uu____21819 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21892 = as_refinement false env t11  in
                       (match uu____21892 with
                        | (x12,phi11) ->
                            let uu____21900 = as_refinement false env t21  in
                            (match uu____21900 with
                             | (x22,phi21) ->
                                 ((let uu____21909 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21909
                                   then
                                     ((let uu____21914 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21916 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21918 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21914
                                         uu____21916 uu____21918);
                                      (let uu____21921 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21923 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21925 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21921
                                         uu____21923 uu____21925))
                                   else ());
                                  (let uu____21930 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21930 with
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
                                         let uu____22001 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22001
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22013 =
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
                                         (let uu____22026 =
                                            let uu____22029 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22029
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22026
                                            (p_guard base_prob));
                                         (let uu____22048 =
                                            let uu____22051 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22051
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22048
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22070 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22070)
                                          in
                                       let has_uvars =
                                         (let uu____22075 =
                                            let uu____22077 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22077
                                             in
                                          Prims.op_Negation uu____22075) ||
                                           (let uu____22081 =
                                              let uu____22083 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22083
                                               in
                                            Prims.op_Negation uu____22081)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22087 =
                                           let uu____22092 =
                                             let uu____22101 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22101]  in
                                           mk_t_problem wl1 uu____22092 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22087 with
                                          | (ref_prob,wl2) ->
                                              let uu____22123 =
                                                solve env1
                                                  (let uu___3094_22125 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3094_22125.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3094_22125.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3094_22125.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3094_22125.tcenv);
                                                     wl_implicits =
                                                       (uu___3094_22125.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22123 with
                                               | Failed (prob,msg) ->
                                                   if
                                                     ((Prims.op_Negation
                                                         env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                        && has_uvars)
                                                       ||
                                                       (Prims.op_Negation
                                                          wl2.smt_ok)
                                                   then giveup env1 msg prob
                                                   else fallback ()
                                               | Success uu____22139 ->
                                                   let guard =
                                                     let uu____22147 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22147
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3105_22156 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3105_22156.attempting);
                                                       wl_deferred =
                                                         (uu___3105_22156.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3105_22156.defer_ok);
                                                       smt_ok =
                                                         (uu___3105_22156.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3105_22156.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3105_22156.tcenv);
                                                       wl_implicits =
                                                         (uu___3105_22156.wl_implicits)
                                                     }  in
                                                   let uu____22158 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22158))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22161,FStar_Syntax_Syntax.Tm_uvar uu____22162) ->
                  let uu____22187 = destruct_flex_t t1 wl  in
                  (match uu____22187 with
                   | (f1,wl1) ->
                       let uu____22194 = destruct_flex_t t2 wl1  in
                       (match uu____22194 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22201;
                    FStar_Syntax_Syntax.pos = uu____22202;
                    FStar_Syntax_Syntax.vars = uu____22203;_},uu____22204),FStar_Syntax_Syntax.Tm_uvar
                 uu____22205) ->
                  let uu____22254 = destruct_flex_t t1 wl  in
                  (match uu____22254 with
                   | (f1,wl1) ->
                       let uu____22261 = destruct_flex_t t2 wl1  in
                       (match uu____22261 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22268,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22269;
                    FStar_Syntax_Syntax.pos = uu____22270;
                    FStar_Syntax_Syntax.vars = uu____22271;_},uu____22272))
                  ->
                  let uu____22321 = destruct_flex_t t1 wl  in
                  (match uu____22321 with
                   | (f1,wl1) ->
                       let uu____22328 = destruct_flex_t t2 wl1  in
                       (match uu____22328 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22335;
                    FStar_Syntax_Syntax.pos = uu____22336;
                    FStar_Syntax_Syntax.vars = uu____22337;_},uu____22338),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22339;
                    FStar_Syntax_Syntax.pos = uu____22340;
                    FStar_Syntax_Syntax.vars = uu____22341;_},uu____22342))
                  ->
                  let uu____22415 = destruct_flex_t t1 wl  in
                  (match uu____22415 with
                   | (f1,wl1) ->
                       let uu____22422 = destruct_flex_t t2 wl1  in
                       (match uu____22422 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22429,uu____22430) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22443 = destruct_flex_t t1 wl  in
                  (match uu____22443 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22450;
                    FStar_Syntax_Syntax.pos = uu____22451;
                    FStar_Syntax_Syntax.vars = uu____22452;_},uu____22453),uu____22454)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22491 = destruct_flex_t t1 wl  in
                  (match uu____22491 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22498,FStar_Syntax_Syntax.Tm_uvar uu____22499) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22512,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22513;
                    FStar_Syntax_Syntax.pos = uu____22514;
                    FStar_Syntax_Syntax.vars = uu____22515;_},uu____22516))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22553,FStar_Syntax_Syntax.Tm_arrow uu____22554) ->
                  solve_t' env
                    (let uu___3205_22582 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3205_22582.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3205_22582.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3205_22582.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3205_22582.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3205_22582.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3205_22582.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3205_22582.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3205_22582.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3205_22582.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22583;
                    FStar_Syntax_Syntax.pos = uu____22584;
                    FStar_Syntax_Syntax.vars = uu____22585;_},uu____22586),FStar_Syntax_Syntax.Tm_arrow
                 uu____22587) ->
                  solve_t' env
                    (let uu___3205_22639 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3205_22639.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3205_22639.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3205_22639.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3205_22639.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3205_22639.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3205_22639.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3205_22639.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3205_22639.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3205_22639.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22640,FStar_Syntax_Syntax.Tm_uvar uu____22641) ->
                  let uu____22654 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22654
              | (uu____22655,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22656;
                    FStar_Syntax_Syntax.pos = uu____22657;
                    FStar_Syntax_Syntax.vars = uu____22658;_},uu____22659))
                  ->
                  let uu____22696 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22696
              | (FStar_Syntax_Syntax.Tm_uvar uu____22697,uu____22698) ->
                  let uu____22711 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22711
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22712;
                    FStar_Syntax_Syntax.pos = uu____22713;
                    FStar_Syntax_Syntax.vars = uu____22714;_},uu____22715),uu____22716)
                  ->
                  let uu____22753 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22753
              | (FStar_Syntax_Syntax.Tm_refine uu____22754,uu____22755) ->
                  let t21 =
                    let uu____22763 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22763  in
                  solve_t env
                    (let uu___3240_22789 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3240_22789.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3240_22789.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3240_22789.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3240_22789.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3240_22789.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3240_22789.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3240_22789.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3240_22789.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3240_22789.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22790,FStar_Syntax_Syntax.Tm_refine uu____22791) ->
                  let t11 =
                    let uu____22799 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22799  in
                  solve_t env
                    (let uu___3247_22825 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3247_22825.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3247_22825.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3247_22825.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3247_22825.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3247_22825.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3247_22825.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3247_22825.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3247_22825.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3247_22825.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22907 =
                    let uu____22908 = guard_of_prob env wl problem t1 t2  in
                    match uu____22908 with
                    | (guard,wl1) ->
                        let uu____22915 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22915
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23134 = br1  in
                        (match uu____23134 with
                         | (p1,w1,uu____23163) ->
                             let uu____23180 = br2  in
                             (match uu____23180 with
                              | (p2,w2,uu____23203) ->
                                  let uu____23208 =
                                    let uu____23210 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23210  in
                                  if uu____23208
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23237 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23237 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23274 = br2  in
                                         (match uu____23274 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23307 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23307
                                                 in
                                              let uu____23312 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23343,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23364) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23423 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23423 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23312
                                                (fun uu____23495  ->
                                                   match uu____23495 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23532 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23532
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23553
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23553
                                                              then
                                                                let uu____23558
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23560
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23558
                                                                  uu____23560
                                                              else ());
                                                             (let uu____23566
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23566
                                                                (fun
                                                                   uu____23602
                                                                    ->
                                                                   match uu____23602
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
                    | uu____23731 -> FStar_Pervasives_Native.None  in
                  let uu____23772 = solve_branches wl brs1 brs2  in
                  (match uu____23772 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23798 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23798 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23825 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23825 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23859 =
                                FStar_List.map
                                  (fun uu____23871  ->
                                     match uu____23871 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23859  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23880 =
                              let uu____23881 =
                                let uu____23882 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23882
                                  (let uu___3346_23890 = wl3  in
                                   {
                                     attempting =
                                       (uu___3346_23890.attempting);
                                     wl_deferred =
                                       (uu___3346_23890.wl_deferred);
                                     ctr = (uu___3346_23890.ctr);
                                     defer_ok = (uu___3346_23890.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3346_23890.umax_heuristic_ok);
                                     tcenv = (uu___3346_23890.tcenv);
                                     wl_implicits =
                                       (uu___3346_23890.wl_implicits)
                                   })
                                 in
                              solve env uu____23881  in
                            (match uu____23880 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23895 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23904 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23904 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23907,uu____23908) ->
                  let head1 =
                    let uu____23932 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23932
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____23978 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____23978
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24024 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24024
                    then
                      let uu____24028 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24030 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24032 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24028 uu____24030 uu____24032
                    else ());
                   (let no_free_uvars t =
                      (let uu____24046 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24046) &&
                        (let uu____24050 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24050)
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
                      let uu____24069 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24069 = FStar_Syntax_Util.Equal  in
                    let uu____24070 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24070
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24074 = equal t1 t2  in
                         (if uu____24074
                          then
                            let uu____24077 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24077
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24082 =
                            let uu____24089 = equal t1 t2  in
                            if uu____24089
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24102 = mk_eq2 wl env orig t1 t2  in
                               match uu____24102 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24082 with
                          | (guard,wl1) ->
                              let uu____24123 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24123))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24126,uu____24127) ->
                  let head1 =
                    let uu____24135 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24135
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24181 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24181
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24227 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24227
                    then
                      let uu____24231 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24233 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24235 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24231 uu____24233 uu____24235
                    else ());
                   (let no_free_uvars t =
                      (let uu____24249 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24249) &&
                        (let uu____24253 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24253)
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
                      let uu____24272 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24272 = FStar_Syntax_Util.Equal  in
                    let uu____24273 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24273
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24277 = equal t1 t2  in
                         (if uu____24277
                          then
                            let uu____24280 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24280
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24285 =
                            let uu____24292 = equal t1 t2  in
                            if uu____24292
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24305 = mk_eq2 wl env orig t1 t2  in
                               match uu____24305 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24285 with
                          | (guard,wl1) ->
                              let uu____24326 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24326))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24329,uu____24330) ->
                  let head1 =
                    let uu____24332 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24332
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24378 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24378
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24424 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24424
                    then
                      let uu____24428 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24430 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24432 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24428 uu____24430 uu____24432
                    else ());
                   (let no_free_uvars t =
                      (let uu____24446 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24446) &&
                        (let uu____24450 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24450)
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
                      let uu____24469 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24469 = FStar_Syntax_Util.Equal  in
                    let uu____24470 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24470
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24474 = equal t1 t2  in
                         (if uu____24474
                          then
                            let uu____24477 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24477
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24482 =
                            let uu____24489 = equal t1 t2  in
                            if uu____24489
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24502 = mk_eq2 wl env orig t1 t2  in
                               match uu____24502 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24482 with
                          | (guard,wl1) ->
                              let uu____24523 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24523))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24526,uu____24527) ->
                  let head1 =
                    let uu____24529 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24529
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24575 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24575
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24621 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24621
                    then
                      let uu____24625 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24627 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24629 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24625 uu____24627 uu____24629
                    else ());
                   (let no_free_uvars t =
                      (let uu____24643 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24643) &&
                        (let uu____24647 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24647)
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
                      let uu____24666 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24666 = FStar_Syntax_Util.Equal  in
                    let uu____24667 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24667
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24671 = equal t1 t2  in
                         (if uu____24671
                          then
                            let uu____24674 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24674
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24679 =
                            let uu____24686 = equal t1 t2  in
                            if uu____24686
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24699 = mk_eq2 wl env orig t1 t2  in
                               match uu____24699 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24679 with
                          | (guard,wl1) ->
                              let uu____24720 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24720))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24723,uu____24724) ->
                  let head1 =
                    let uu____24726 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24726
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24772 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24772
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24818 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24818
                    then
                      let uu____24822 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24824 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24826 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24822 uu____24824 uu____24826
                    else ());
                   (let no_free_uvars t =
                      (let uu____24840 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24840) &&
                        (let uu____24844 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24844)
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
                      let uu____24863 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24863 = FStar_Syntax_Util.Equal  in
                    let uu____24864 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24864
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24868 = equal t1 t2  in
                         (if uu____24868
                          then
                            let uu____24871 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24871
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24876 =
                            let uu____24883 = equal t1 t2  in
                            if uu____24883
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24896 = mk_eq2 wl env orig t1 t2  in
                               match uu____24896 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24876 with
                          | (guard,wl1) ->
                              let uu____24917 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24917))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24920,uu____24921) ->
                  let head1 =
                    let uu____24939 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24939
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24985 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24985
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25031 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25031
                    then
                      let uu____25035 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25037 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25039 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25035 uu____25037 uu____25039
                    else ());
                   (let no_free_uvars t =
                      (let uu____25053 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25053) &&
                        (let uu____25057 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25057)
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
                      let uu____25076 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25076 = FStar_Syntax_Util.Equal  in
                    let uu____25077 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25077
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25081 = equal t1 t2  in
                         (if uu____25081
                          then
                            let uu____25084 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25084
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25089 =
                            let uu____25096 = equal t1 t2  in
                            if uu____25096
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25109 = mk_eq2 wl env orig t1 t2  in
                               match uu____25109 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25089 with
                          | (guard,wl1) ->
                              let uu____25130 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25130))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25133,FStar_Syntax_Syntax.Tm_match uu____25134) ->
                  let head1 =
                    let uu____25158 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25158
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25204 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25204
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25250 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25250
                    then
                      let uu____25254 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25256 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25258 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25254 uu____25256 uu____25258
                    else ());
                   (let no_free_uvars t =
                      (let uu____25272 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25272) &&
                        (let uu____25276 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25276)
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
                      let uu____25295 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25295 = FStar_Syntax_Util.Equal  in
                    let uu____25296 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25296
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25300 = equal t1 t2  in
                         (if uu____25300
                          then
                            let uu____25303 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25303
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25308 =
                            let uu____25315 = equal t1 t2  in
                            if uu____25315
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25328 = mk_eq2 wl env orig t1 t2  in
                               match uu____25328 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25308 with
                          | (guard,wl1) ->
                              let uu____25349 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25349))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25352,FStar_Syntax_Syntax.Tm_uinst uu____25353) ->
                  let head1 =
                    let uu____25361 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25361
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25407 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25407
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25453 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25453
                    then
                      let uu____25457 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25459 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25461 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25457 uu____25459 uu____25461
                    else ());
                   (let no_free_uvars t =
                      (let uu____25475 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25475) &&
                        (let uu____25479 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25479)
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
                      let uu____25498 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25498 = FStar_Syntax_Util.Equal  in
                    let uu____25499 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25499
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25503 = equal t1 t2  in
                         (if uu____25503
                          then
                            let uu____25506 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25506
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25511 =
                            let uu____25518 = equal t1 t2  in
                            if uu____25518
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25531 = mk_eq2 wl env orig t1 t2  in
                               match uu____25531 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25511 with
                          | (guard,wl1) ->
                              let uu____25552 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25552))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25555,FStar_Syntax_Syntax.Tm_name uu____25556) ->
                  let head1 =
                    let uu____25558 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25558
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25604 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25604
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25644 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25644
                    then
                      let uu____25648 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25650 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25652 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25648 uu____25650 uu____25652
                    else ());
                   (let no_free_uvars t =
                      (let uu____25666 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25666) &&
                        (let uu____25670 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25670)
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
                      let uu____25689 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25689 = FStar_Syntax_Util.Equal  in
                    let uu____25690 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25690
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25694 = equal t1 t2  in
                         (if uu____25694
                          then
                            let uu____25697 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25697
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25702 =
                            let uu____25709 = equal t1 t2  in
                            if uu____25709
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25722 = mk_eq2 wl env orig t1 t2  in
                               match uu____25722 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25702 with
                          | (guard,wl1) ->
                              let uu____25743 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25743))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25746,FStar_Syntax_Syntax.Tm_constant uu____25747) ->
                  let head1 =
                    let uu____25749 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25749
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25789 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25789
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25829 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25829
                    then
                      let uu____25833 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25835 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25837 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25833 uu____25835 uu____25837
                    else ());
                   (let no_free_uvars t =
                      (let uu____25851 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25851) &&
                        (let uu____25855 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25855)
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
                      let uu____25874 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25874 = FStar_Syntax_Util.Equal  in
                    let uu____25875 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25875
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25879 = equal t1 t2  in
                         (if uu____25879
                          then
                            let uu____25882 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25882
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25887 =
                            let uu____25894 = equal t1 t2  in
                            if uu____25894
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25907 = mk_eq2 wl env orig t1 t2  in
                               match uu____25907 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25887 with
                          | (guard,wl1) ->
                              let uu____25928 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25928))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25931,FStar_Syntax_Syntax.Tm_fvar uu____25932) ->
                  let head1 =
                    let uu____25934 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25934
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25980 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25980
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26026 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26026
                    then
                      let uu____26030 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26032 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26034 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26030 uu____26032 uu____26034
                    else ());
                   (let no_free_uvars t =
                      (let uu____26048 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26048) &&
                        (let uu____26052 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26052)
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
                      let uu____26071 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26071 = FStar_Syntax_Util.Equal  in
                    let uu____26072 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26072
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26076 = equal t1 t2  in
                         (if uu____26076
                          then
                            let uu____26079 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26079
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26084 =
                            let uu____26091 = equal t1 t2  in
                            if uu____26091
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26104 = mk_eq2 wl env orig t1 t2  in
                               match uu____26104 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26084 with
                          | (guard,wl1) ->
                              let uu____26125 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26125))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26128,FStar_Syntax_Syntax.Tm_app uu____26129) ->
                  let head1 =
                    let uu____26147 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26147
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26187 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26187
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26227 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26227
                    then
                      let uu____26231 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26233 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26235 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26231 uu____26233 uu____26235
                    else ());
                   (let no_free_uvars t =
                      (let uu____26249 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26249) &&
                        (let uu____26253 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26253)
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
                      let uu____26272 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26272 = FStar_Syntax_Util.Equal  in
                    let uu____26273 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26273
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26277 = equal t1 t2  in
                         (if uu____26277
                          then
                            let uu____26280 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26280
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26285 =
                            let uu____26292 = equal t1 t2  in
                            if uu____26292
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26305 = mk_eq2 wl env orig t1 t2  in
                               match uu____26305 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26285 with
                          | (guard,wl1) ->
                              let uu____26326 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26326))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26329,FStar_Syntax_Syntax.Tm_let uu____26330) ->
                  let uu____26357 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26357
                  then
                    let uu____26360 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26360
                  else
                    (let uu____26363 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26363 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26366,uu____26367) ->
                  let uu____26381 =
                    let uu____26387 =
                      let uu____26389 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26391 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26393 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26395 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26389 uu____26391 uu____26393 uu____26395
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26387)
                     in
                  FStar_Errors.raise_error uu____26381
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26399,FStar_Syntax_Syntax.Tm_let uu____26400) ->
                  let uu____26414 =
                    let uu____26420 =
                      let uu____26422 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26424 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26426 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26428 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26422 uu____26424 uu____26426 uu____26428
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26420)
                     in
                  FStar_Errors.raise_error uu____26414
                    t1.FStar_Syntax_Syntax.pos
              | uu____26432 ->
                  let uu____26437 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26437 orig))))

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
          (let uu____26503 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26503
           then
             let uu____26508 =
               let uu____26510 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26510  in
             let uu____26511 =
               let uu____26513 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26513  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26508 uu____26511
           else ());
          (let uu____26517 =
             let uu____26519 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26519  in
           if uu____26517
           then
             let uu____26522 =
               FStar_Thunk.mk
                 (fun uu____26527  ->
                    let uu____26528 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26530 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26528 uu____26530)
                in
             giveup env uu____26522 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26552 =
                  FStar_Thunk.mk
                    (fun uu____26557  ->
                       let uu____26558 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26560 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26558 uu____26560)
                   in
                giveup env uu____26552 orig)
             else
               (let uu____26565 =
                  FStar_List.fold_left2
                    (fun uu____26586  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26586 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26607 =
                                 let uu____26612 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26613 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26612
                                   FStar_TypeChecker_Common.EQ uu____26613
                                   "effect universes"
                                  in
                               (match uu____26607 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26565 with
                | (univ_sub_probs,wl1) ->
                    let uu____26633 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26633 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26641 =
                           FStar_List.fold_right2
                             (fun uu____26678  ->
                                fun uu____26679  ->
                                  fun uu____26680  ->
                                    match (uu____26678, uu____26679,
                                            uu____26680)
                                    with
                                    | ((a1,uu____26724),(a2,uu____26726),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26759 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26759 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26641 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26786 =
                                  let uu____26789 =
                                    let uu____26792 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26792
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26789
                                   in
                                FStar_List.append univ_sub_probs uu____26786
                                 in
                              let guard =
                                let guard =
                                  let uu____26814 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26814  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3498_26823 = wl3  in
                                {
                                  attempting = (uu___3498_26823.attempting);
                                  wl_deferred = (uu___3498_26823.wl_deferred);
                                  ctr = (uu___3498_26823.ctr);
                                  defer_ok = (uu___3498_26823.defer_ok);
                                  smt_ok = (uu___3498_26823.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3498_26823.umax_heuristic_ok);
                                  tcenv = (uu___3498_26823.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26825 = attempt sub_probs wl5  in
                              solve env uu____26825))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26843 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26843
           then
             let uu____26848 =
               let uu____26850 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26850
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26852 =
               let uu____26854 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26854
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26848 uu____26852
           else ());
          (let uu____26859 =
             let uu____26864 =
               let uu____26869 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26869
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26864
               (fun uu____26886  ->
                  match uu____26886 with
                  | (c,g) ->
                      let uu____26897 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26897, g))
              in
           match uu____26859 with
           | (c12,g_lift) ->
               ((let uu____26901 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26901
                 then
                   let uu____26906 =
                     let uu____26908 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26908
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26910 =
                     let uu____26912 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26912
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26906 uu____26910
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3518_26922 = wl  in
                     {
                       attempting = (uu___3518_26922.attempting);
                       wl_deferred = (uu___3518_26922.wl_deferred);
                       ctr = (uu___3518_26922.ctr);
                       defer_ok = (uu___3518_26922.defer_ok);
                       smt_ok = (uu___3518_26922.smt_ok);
                       umax_heuristic_ok =
                         (uu___3518_26922.umax_heuristic_ok);
                       tcenv = (uu___3518_26922.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26923 =
                     let rec is_uvar1 t =
                       let uu____26937 =
                         let uu____26938 = FStar_Syntax_Subst.compress t  in
                         uu____26938.FStar_Syntax_Syntax.n  in
                       match uu____26937 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26942 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26957) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26963) ->
                           is_uvar1 t1
                       | uu____26988 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27022  ->
                          fun uu____27023  ->
                            fun uu____27024  ->
                              match (uu____27022, uu____27023, uu____27024)
                              with
                              | ((a1,uu____27068),(a2,uu____27070),(is_sub_probs,wl2))
                                  ->
                                  let uu____27103 = is_uvar1 a1  in
                                  if uu____27103
                                  then
                                    ((let uu____27113 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27113
                                      then
                                        let uu____27118 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27120 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27118 uu____27120
                                      else ());
                                     (let uu____27125 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27125 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26923 with
                   | (is_sub_probs,wl2) ->
                       let uu____27153 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27153 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27161 =
                              let uu____27166 =
                                let uu____27167 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27167
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27166
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27161 with
                             | (uu____27174,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27185 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27187 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27185 s uu____27187
                                    in
                                 let uu____27190 =
                                   let uu____27219 =
                                     let uu____27220 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27220.FStar_Syntax_Syntax.n  in
                                   match uu____27219 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27280 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27280 with
                                        | (a::bs1,c3) ->
                                            let uu____27336 =
                                              let uu____27355 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27355
                                                (fun uu____27459  ->
                                                   match uu____27459 with
                                                   | (l1,l2) ->
                                                       let uu____27532 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27532))
                                               in
                                            (match uu____27336 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27637 ->
                                       let uu____27638 =
                                         let uu____27644 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27644)
                                          in
                                       FStar_Errors.raise_error uu____27638 r
                                    in
                                 (match uu____27190 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27720 =
                                        let uu____27727 =
                                          let uu____27728 =
                                            let uu____27729 =
                                              let uu____27736 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27736,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27729
                                             in
                                          [uu____27728]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27727
                                          (fun b  ->
                                             let uu____27752 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27754 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27756 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27752 uu____27754
                                               uu____27756) r
                                         in
                                      (match uu____27720 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27766 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27766
                                             then
                                               let uu____27771 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27780 =
                                                          let uu____27782 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27782
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27780) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27771
                                             else ());
                                            (let wl4 =
                                               let uu___3590_27790 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3590_27790.attempting);
                                                 wl_deferred =
                                                   (uu___3590_27790.wl_deferred);
                                                 ctr = (uu___3590_27790.ctr);
                                                 defer_ok =
                                                   (uu___3590_27790.defer_ok);
                                                 smt_ok =
                                                   (uu___3590_27790.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3590_27790.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3590_27790.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27815 =
                                                        let uu____27822 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27822, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27815) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27839 =
                                               let f_sort_is =
                                                 let uu____27849 =
                                                   let uu____27850 =
                                                     let uu____27853 =
                                                       let uu____27854 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27854.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27853
                                                      in
                                                   uu____27850.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27849 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27865,uu____27866::is)
                                                     ->
                                                     let uu____27908 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27908
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27941 ->
                                                     let uu____27942 =
                                                       let uu____27948 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27948)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27942 r
                                                  in
                                               let uu____27954 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____27989  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____27989
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28010 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28010
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27954
                                                in
                                             match uu____27839 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28035 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28035
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28036 =
                                                   let g_sort_is =
                                                     let uu____28046 =
                                                       let uu____28047 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28047.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28046 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28052,uu____28053::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28113 ->
                                                         let uu____28114 =
                                                           let uu____28120 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28120)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28114 r
                                                      in
                                                   let uu____28126 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28161  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28161
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28182
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28182
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28126
                                                    in
                                                 (match uu____28036 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28209 =
                                                          let uu____28214 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28215 =
                                                            let uu____28216 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28216
                                                             in
                                                          (uu____28214,
                                                            uu____28215)
                                                           in
                                                        match uu____28209
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28244 =
                                                          let uu____28247 =
                                                            let uu____28250 =
                                                              let uu____28253
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28253
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28250
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28247
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28244
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28277 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28277
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
                                                        let uu____28288 =
                                                          let uu____28291 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28294  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28294)
                                                            uu____28291
                                                           in
                                                        solve_prob orig
                                                          uu____28288 [] wl6
                                                         in
                                                      let uu____28295 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28295))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28318 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28320 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28320]
              | x -> x  in
            let c12 =
              let uu___3656_28323 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3656_28323.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3656_28323.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3656_28323.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3656_28323.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28324 =
              let uu____28329 =
                FStar_All.pipe_right
                  (let uu___3659_28331 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3659_28331.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3659_28331.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3659_28331.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3659_28331.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28329
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28324
              (fun uu____28345  ->
                 match uu____28345 with
                 | (c,g) ->
                     let uu____28352 =
                       let uu____28354 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28354  in
                     if uu____28352
                     then
                       let uu____28357 =
                         let uu____28363 =
                           let uu____28365 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28367 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28365 uu____28367
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28363)
                          in
                       FStar_Errors.raise_error uu____28357 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28373 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28373
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28379 = lift_c1 ()  in
               solve_eq uu____28379 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28388  ->
                         match uu___31_28388 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28393 -> false))
                  in
               let uu____28395 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28425)::uu____28426,(wp2,uu____28428)::uu____28429)
                     -> (wp1, wp2)
                 | uu____28502 ->
                     let uu____28527 =
                       let uu____28533 =
                         let uu____28535 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28537 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28535 uu____28537
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28533)
                        in
                     FStar_Errors.raise_error uu____28527
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28395 with
               | (wpc1,wpc2) ->
                   let uu____28547 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28547
                   then
                     let uu____28550 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28550 wl
                   else
                     (let uu____28554 =
                        let uu____28561 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28561  in
                      match uu____28554 with
                      | (c2_decl,qualifiers) ->
                          let uu____28582 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28582
                          then
                            let c1_repr =
                              let uu____28589 =
                                let uu____28590 =
                                  let uu____28591 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28591  in
                                let uu____28592 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28590 uu____28592
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28589
                               in
                            let c2_repr =
                              let uu____28595 =
                                let uu____28596 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28597 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28596 uu____28597
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28595
                               in
                            let uu____28599 =
                              let uu____28604 =
                                let uu____28606 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28608 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28606
                                  uu____28608
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28604
                               in
                            (match uu____28599 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28614 = attempt [prob] wl2  in
                                 solve env uu____28614)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28634 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28634
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28657 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28657
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
                                        let uu____28667 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28667 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28674 =
                                        let uu____28681 =
                                          let uu____28682 =
                                            let uu____28699 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28702 =
                                              let uu____28713 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28713; wpc1_2]  in
                                            (uu____28699, uu____28702)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28682
                                           in
                                        FStar_Syntax_Syntax.mk uu____28681
                                         in
                                      uu____28674
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
                                     let uu____28762 =
                                       let uu____28769 =
                                         let uu____28770 =
                                           let uu____28787 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28790 =
                                             let uu____28801 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28810 =
                                               let uu____28821 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28821; wpc1_2]  in
                                             uu____28801 :: uu____28810  in
                                           (uu____28787, uu____28790)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28770
                                          in
                                       FStar_Syntax_Syntax.mk uu____28769  in
                                     uu____28762 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28875 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28875
                              then
                                let uu____28880 =
                                  let uu____28882 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28882
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28880
                              else ());
                             (let uu____28886 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28886 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28895 =
                                      let uu____28898 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28901  ->
                                           FStar_Pervasives_Native.Some
                                             _28901) uu____28898
                                       in
                                    solve_prob orig uu____28895 [] wl1  in
                                  let uu____28902 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28902))))
           in
        let uu____28903 = FStar_Util.physical_equality c1 c2  in
        if uu____28903
        then
          let uu____28906 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28906
        else
          ((let uu____28910 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28910
            then
              let uu____28915 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28917 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28915
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28917
            else ());
           (let uu____28922 =
              let uu____28931 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28934 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28931, uu____28934)  in
            match uu____28922 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28952),FStar_Syntax_Syntax.Total
                    (t2,uu____28954)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28971 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28971 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28973,FStar_Syntax_Syntax.Total uu____28974) ->
                     let uu____28991 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____28991 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____28995),FStar_Syntax_Syntax.Total
                    (t2,uu____28997)) ->
                     let uu____29014 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29014 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29017),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29019)) ->
                     let uu____29036 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29036 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29039),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29041)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29058 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29058 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29061),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29063)) ->
                     let uu____29080 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29080 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29083,FStar_Syntax_Syntax.Comp uu____29084) ->
                     let uu____29093 =
                       let uu___3783_29096 = problem  in
                       let uu____29099 =
                         let uu____29100 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29100
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3783_29096.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29099;
                         FStar_TypeChecker_Common.relation =
                           (uu___3783_29096.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3783_29096.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3783_29096.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3783_29096.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3783_29096.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3783_29096.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3783_29096.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3783_29096.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29093 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29101,FStar_Syntax_Syntax.Comp uu____29102) ->
                     let uu____29111 =
                       let uu___3783_29114 = problem  in
                       let uu____29117 =
                         let uu____29118 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29118
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3783_29114.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29117;
                         FStar_TypeChecker_Common.relation =
                           (uu___3783_29114.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3783_29114.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3783_29114.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3783_29114.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3783_29114.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3783_29114.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3783_29114.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3783_29114.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29111 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29119,FStar_Syntax_Syntax.GTotal uu____29120) ->
                     let uu____29129 =
                       let uu___3795_29132 = problem  in
                       let uu____29135 =
                         let uu____29136 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29136
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3795_29132.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3795_29132.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3795_29132.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29135;
                         FStar_TypeChecker_Common.element =
                           (uu___3795_29132.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3795_29132.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3795_29132.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3795_29132.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3795_29132.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3795_29132.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29129 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29137,FStar_Syntax_Syntax.Total uu____29138) ->
                     let uu____29147 =
                       let uu___3795_29150 = problem  in
                       let uu____29153 =
                         let uu____29154 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29154
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3795_29150.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3795_29150.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3795_29150.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29153;
                         FStar_TypeChecker_Common.element =
                           (uu___3795_29150.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3795_29150.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3795_29150.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3795_29150.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3795_29150.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3795_29150.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29147 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29155,FStar_Syntax_Syntax.Comp uu____29156) ->
                     let uu____29157 =
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
                     if uu____29157
                     then
                       let uu____29160 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29160 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29167 =
                            let uu____29172 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29172
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29181 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29182 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29181, uu____29182))
                             in
                          match uu____29167 with
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
                           (let uu____29190 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29190
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29198 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29198 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29201 =
                                  FStar_Thunk.mk
                                    (fun uu____29206  ->
                                       let uu____29207 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29209 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29207 uu____29209)
                                   in
                                giveup env uu____29201 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29220 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29220 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29270 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29270 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29295 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29326  ->
                match uu____29326 with
                | (u1,u2) ->
                    let uu____29334 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29336 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29334 uu____29336))
         in
      FStar_All.pipe_right uu____29295 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29373,[])) when
          let uu____29400 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29400 -> "{}"
      | uu____29403 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29430 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29430
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29442 =
              FStar_List.map
                (fun uu____29455  ->
                   match uu____29455 with
                   | (uu____29462,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29442 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29473 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29473 imps
  
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
                  let uu____29530 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29530
                  then
                    let uu____29538 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29540 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29538
                      (rel_to_string rel) uu____29540
                  else "TOP"  in
                let uu____29546 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29546 with
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
              let uu____29606 =
                let uu____29609 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29612  -> FStar_Pervasives_Native.Some _29612)
                  uu____29609
                 in
              FStar_Syntax_Syntax.new_bv uu____29606 t1  in
            let uu____29613 =
              let uu____29618 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29618
               in
            match uu____29613 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____29676 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29676
         then
           let uu____29681 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29681
         else ());
        (let uu____29688 =
           FStar_Util.record_time (fun uu____29695  -> solve env probs)  in
         match uu____29688 with
         | (sol,ms) ->
             ((let uu____29707 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29707
               then
                 let uu____29712 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29712
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29725 =
                     FStar_Util.record_time
                       (fun uu____29732  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29725 with
                    | ((),ms1) ->
                        ((let uu____29743 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29743
                          then
                            let uu____29748 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29748
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29760 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29760
                     then
                       let uu____29767 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29767
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
          ((let uu____29793 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29793
            then
              let uu____29798 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29798
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29806 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29806
             then
               let uu____29811 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29811
             else ());
            (let f2 =
               let uu____29817 =
                 let uu____29818 = FStar_Syntax_Util.unmeta f1  in
                 uu____29818.FStar_Syntax_Syntax.n  in
               match uu____29817 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29822 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3912_29823 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3912_29823.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3912_29823.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3912_29823.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred *
        FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29866 =
              let uu____29867 =
                let uu____29868 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29869  ->
                       FStar_TypeChecker_Common.NonTrivial _29869)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29868;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29867  in
            FStar_All.pipe_left
              (fun _29876  -> FStar_Pervasives_Native.Some _29876)
              uu____29866
  
let with_guard_no_simp :
  'Auu____29886 .
    'Auu____29886 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____29926 =
              let uu____29927 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29928  -> FStar_TypeChecker_Common.NonTrivial _29928)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29927;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29926
  
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
          (let uu____29961 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29961
           then
             let uu____29966 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29968 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29966
               uu____29968
           else ());
          (let uu____29973 =
             let uu____29978 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____29978
              in
           match uu____29973 with
           | (prob,wl) ->
               let g =
                 let uu____29986 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____29994  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____29986  in
               ((let uu____30012 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30012
                 then
                   let uu____30017 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30017
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
        let uu____30038 = try_teq true env t1 t2  in
        match uu____30038 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30043 = FStar_TypeChecker_Env.get_range env  in
              let uu____30044 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30043 uu____30044);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30052 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30052
              then
                let uu____30057 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30059 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30061 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30057
                  uu____30059 uu____30061
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
        (let uu____30085 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30085
         then
           let uu____30090 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30092 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30090
             uu____30092
         else ());
        (let uu____30097 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30097 with
         | (prob,x,wl) ->
             let g =
               let uu____30112 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30121  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30112  in
             ((let uu____30139 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30139
               then
                 let uu____30144 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30144
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30152 =
                     let uu____30153 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30153 g1  in
                   FStar_Pervasives_Native.Some uu____30152)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30175 = FStar_TypeChecker_Env.get_range env  in
          let uu____30176 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30175 uu____30176
  
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
        (let uu____30205 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30205
         then
           let uu____30210 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30212 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30210 uu____30212
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30223 =
           let uu____30230 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30230 "sub_comp"
            in
         match uu____30223 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30243 =
                 FStar_Util.record_time
                   (fun uu____30255  ->
                      let uu____30256 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30265  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30256)
                  in
               match uu____30243 with
               | (r,ms) ->
                   ((let uu____30293 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30293
                     then
                       let uu____30298 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30300 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30302 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30298 uu____30300
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30302
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
      fun uu____30340  ->
        match uu____30340 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30383 =
                 let uu____30389 =
                   let uu____30391 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30393 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30391 uu____30393
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30389)  in
               let uu____30397 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30383 uu____30397)
               in
            let equiv1 v1 v' =
              let uu____30410 =
                let uu____30415 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30416 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30415, uu____30416)  in
              match uu____30410 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30436 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30467 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30467 with
                      | FStar_Syntax_Syntax.U_unif uu____30474 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30503  ->
                                    match uu____30503 with
                                    | (u,v') ->
                                        let uu____30512 = equiv1 v1 v'  in
                                        if uu____30512
                                        then
                                          let uu____30517 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30517 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30538 -> []))
               in
            let uu____30543 =
              let wl =
                let uu___4023_30547 = empty_worklist env  in
                {
                  attempting = (uu___4023_30547.attempting);
                  wl_deferred = (uu___4023_30547.wl_deferred);
                  ctr = (uu___4023_30547.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4023_30547.smt_ok);
                  umax_heuristic_ok = (uu___4023_30547.umax_heuristic_ok);
                  tcenv = (uu___4023_30547.tcenv);
                  wl_implicits = (uu___4023_30547.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30566  ->
                      match uu____30566 with
                      | (lb,v1) ->
                          let uu____30573 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30573 with
                           | USolved wl1 -> ()
                           | uu____30576 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30587 =
              match uu____30587 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30599) -> true
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
                      uu____30623,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30625,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30636) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30644,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30653 -> false)
               in
            let uu____30659 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30676  ->
                      match uu____30676 with
                      | (u,v1) ->
                          let uu____30684 = check_ineq (u, v1)  in
                          if uu____30684
                          then true
                          else
                            ((let uu____30692 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30692
                              then
                                let uu____30697 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30699 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30697
                                  uu____30699
                              else ());
                             false)))
               in
            if uu____30659
            then ()
            else
              ((let uu____30709 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30709
                then
                  ((let uu____30715 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30715);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30727 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30727))
                else ());
               (let uu____30740 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30740))
  
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
        let fail1 uu____30813 =
          match uu____30813 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4100_30836 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4100_30836.attempting);
            wl_deferred = (uu___4100_30836.wl_deferred);
            ctr = (uu___4100_30836.ctr);
            defer_ok;
            smt_ok = (uu___4100_30836.smt_ok);
            umax_heuristic_ok = (uu___4100_30836.umax_heuristic_ok);
            tcenv = (uu___4100_30836.tcenv);
            wl_implicits = (uu___4100_30836.wl_implicits)
          }  in
        (let uu____30839 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30839
         then
           let uu____30844 = FStar_Util.string_of_bool defer_ok  in
           let uu____30846 = wl_to_string wl  in
           let uu____30848 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30844 uu____30846 uu____30848
         else ());
        (let g1 =
           let uu____30854 = solve_and_commit env wl fail1  in
           match uu____30854 with
           | FStar_Pervasives_Native.Some
               (uu____30861::uu____30862,uu____30863) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4115_30892 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4115_30892.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4115_30892.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30893 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4120_30902 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4120_30902.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4120_30902.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4120_30902.FStar_TypeChecker_Common.implicits)
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
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___4132_30979 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4132_30979.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4132_30979.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4132_30979.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30980 =
            let uu____30982 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30982  in
          if uu____30980
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30994 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30995 =
                       let uu____30997 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30997
                        in
                     FStar_Errors.diag uu____30994 uu____30995)
                  else ();
                  (let vc1 =
                     let uu____31003 =
                       let uu____31007 =
                         let uu____31009 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31009  in
                       FStar_Pervasives_Native.Some uu____31007  in
                     FStar_Profiling.profile
                       (fun uu____31012  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31003 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31016 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31017 =
                        let uu____31019 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31019
                         in
                      FStar_Errors.diag uu____31016 uu____31017)
                   else ();
                   (let uu____31025 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31025
                      "discharge_guard'" env vc1);
                   (let uu____31027 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31027 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31036 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31037 =
                                let uu____31039 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31039
                                 in
                              FStar_Errors.diag uu____31036 uu____31037)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31049 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31050 =
                                let uu____31052 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31052
                                 in
                              FStar_Errors.diag uu____31049 uu____31050)
                           else ();
                           (let vcs =
                              let uu____31066 = FStar_Options.use_tactics ()
                                 in
                              if uu____31066
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31088  ->
                                     (let uu____31090 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31090);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31134  ->
                                              match uu____31134 with
                                              | (env1,goal,opts) ->
                                                  let uu____31150 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31150, opts)))))
                              else
                                (let uu____31154 =
                                   let uu____31161 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31161)  in
                                 [uu____31154])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31194  ->
                                    match uu____31194 with
                                    | (env1,goal,opts) ->
                                        let uu____31204 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31204 with
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
                                                (let uu____31215 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31216 =
                                                   let uu____31218 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31220 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31218 uu____31220
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31215 uu____31216)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31227 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31228 =
                                                   let uu____31230 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31230
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31227 uu____31228)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31248 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31248 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31257 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31257
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31271 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31271 with
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
        let uu____31301 = try_teq false env t1 t2  in
        match uu____31301 with
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
            let uu____31345 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31345 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31358 ->
                     let uu____31371 =
                       let uu____31372 = FStar_Syntax_Subst.compress r  in
                       uu____31372.FStar_Syntax_Syntax.n  in
                     (match uu____31371 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31377) ->
                          unresolved ctx_u'
                      | uu____31394 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31418 = acc  in
            match uu____31418 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31437 = hd1  in
                     (match uu____31437 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31448 = unresolved ctx_u  in
                             if uu____31448
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31472 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31472
                                     then
                                       let uu____31476 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31476
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31485 = teq_nosmt env1 t tm
                                          in
                                       match uu____31485 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4245_31495 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4245_31495.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4248_31503 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4248_31503.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4248_31503.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4248_31503.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4252_31514 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4252_31514.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4252_31514.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4252_31514.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4252_31514.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4252_31514.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4252_31514.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4252_31514.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4252_31514.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4252_31514.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4252_31514.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4252_31514.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4252_31514.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4252_31514.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4252_31514.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4252_31514.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4252_31514.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4252_31514.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4252_31514.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4252_31514.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4252_31514.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4252_31514.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4252_31514.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4252_31514.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4252_31514.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4252_31514.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4252_31514.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4252_31514.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4252_31514.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4252_31514.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4252_31514.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4252_31514.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4252_31514.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4252_31514.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4252_31514.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4252_31514.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4252_31514.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4252_31514.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4252_31514.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4252_31514.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4252_31514.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4252_31514.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4252_31514.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4252_31514.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4252_31514.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4252_31514.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4252_31514.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4257_31519 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4257_31519.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4257_31519.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4257_31519.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4257_31519.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4257_31519.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4257_31519.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4257_31519.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4257_31519.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4257_31519.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4257_31519.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4257_31519.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4257_31519.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4257_31519.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4257_31519.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4257_31519.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4257_31519.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4257_31519.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4257_31519.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4257_31519.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4257_31519.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4257_31519.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4257_31519.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4257_31519.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4257_31519.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4257_31519.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4257_31519.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4257_31519.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4257_31519.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4257_31519.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4257_31519.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4257_31519.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4257_31519.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4257_31519.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4257_31519.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4257_31519.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4257_31519.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4257_31519.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31524 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31524
                                   then
                                     let uu____31529 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31531 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31533 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31535 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31529 uu____31531 uu____31533
                                       reason uu____31535
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4263_31542  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31549 =
                                             let uu____31559 =
                                               let uu____31567 =
                                                 let uu____31569 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31571 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31573 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31569 uu____31571
                                                   uu____31573
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31567, r)
                                                in
                                             [uu____31559]  in
                                           FStar_Errors.add_errors
                                             uu____31549);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31592 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31603  ->
                                               let uu____31604 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31606 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31608 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31604 uu____31606
                                                 reason uu____31608)) env2 g1
                                         true
                                        in
                                     match uu____31592 with
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
          let uu___4275_31616 = g  in
          let uu____31617 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4275_31616.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4275_31616.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4275_31616.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31617
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____31657 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31657 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31658 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31658
      | imp::uu____31660 ->
          let uu____31663 =
            let uu____31669 =
              let uu____31671 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31673 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31671 uu____31673
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31669)
             in
          FStar_Errors.raise_error uu____31663
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31693 = teq env t1 t2  in
        force_trivial_guard env uu____31693
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31712 = teq_nosmt env t1 t2  in
        match uu____31712 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4300_31731 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4300_31731.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4300_31731.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4300_31731.FStar_TypeChecker_Common.implicits)
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
        (let uu____31767 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31767
         then
           let uu____31772 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31774 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31772
             uu____31774
         else ());
        (let uu____31779 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31779 with
         | (prob,x,wl) ->
             let g =
               let uu____31798 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31807  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31798  in
             ((let uu____31825 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31825
               then
                 let uu____31830 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31832 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31834 =
                   let uu____31836 = FStar_Util.must g  in
                   guard_to_string env uu____31836  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31830 uu____31832 uu____31834
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
        let uu____31873 = check_subtyping env t1 t2  in
        match uu____31873 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31892 =
              let uu____31893 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31893 g  in
            FStar_Pervasives_Native.Some uu____31892
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31912 = check_subtyping env t1 t2  in
        match uu____31912 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31931 =
              let uu____31932 =
                let uu____31933 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31933]  in
              FStar_TypeChecker_Env.close_guard env uu____31932 g  in
            FStar_Pervasives_Native.Some uu____31931
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31971 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31971
         then
           let uu____31976 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31978 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31976
             uu____31978
         else ());
        (let uu____31983 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31983 with
         | (prob,x,wl) ->
             let g =
               let uu____31998 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32007  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31998  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32028 =
                      let uu____32029 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32029]  in
                    FStar_TypeChecker_Env.close_guard env uu____32028 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32070 = subtype_nosmt env t1 t2  in
        match uu____32070 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  