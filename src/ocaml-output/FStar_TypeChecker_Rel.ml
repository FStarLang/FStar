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
  
let (tgt_ctx_includes_src_ctx :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool)
  =
  fun tgt  ->
    fun src  ->
      let uu____6080 =
        maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
          src.FStar_Syntax_Syntax.ctx_uvar_binders
         in
      match uu____6080 with
      | (pfx,uu____6091) ->
          (FStar_List.length pfx) =
            (FStar_List.length src.FStar_Syntax_Syntax.ctx_uvar_binders)
  
let (tgt_ctx_includes_all_source_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> Prims.bool)
  =
  fun tgt  ->
    fun sources  -> FStar_List.for_all (tgt_ctx_includes_src_ctx tgt) sources
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6144 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6144 with
        | (pfx,uu____6154) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6166 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6166 with
             | (uu____6174,src',wl1) ->
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
                 | uu____6288 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6289 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6353  ->
                  fun uu____6354  ->
                    match (uu____6353, uu____6354) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6457 =
                          let uu____6459 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6459
                           in
                        if uu____6457
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6493 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6493
                           then
                             let uu____6510 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6510)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6289 with | (isect,uu____6560) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6596 'Auu____6597 .
    (FStar_Syntax_Syntax.bv * 'Auu____6596) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6597) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6655  ->
              fun uu____6656  ->
                match (uu____6655, uu____6656) with
                | ((a,uu____6675),(b,uu____6677)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6693 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6693) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6724  ->
           match uu____6724 with
           | (y,uu____6731) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6741 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6741) Prims.list ->
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
                   let uu____6903 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6903
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6936 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____6988 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7032 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7053 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7061  ->
    match uu___22_7061 with
    | MisMatch (d1,d2) ->
        let uu____7073 =
          let uu____7075 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7077 =
            let uu____7079 =
              let uu____7081 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7081 ")"  in
            Prims.op_Hat ") (" uu____7079  in
          Prims.op_Hat uu____7075 uu____7077  in
        Prims.op_Hat "MisMatch (" uu____7073
    | HeadMatch u ->
        let uu____7088 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7088
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7097  ->
    match uu___23_7097 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7114 -> HeadMatch false
  
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
          let uu____7136 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7136 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7147 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7171 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7181 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7208 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7208
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7209 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7210 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7211 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7224 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7238 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7262) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7268,uu____7269) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7311) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7336;
             FStar_Syntax_Syntax.index = uu____7337;
             FStar_Syntax_Syntax.sort = t2;_},uu____7339)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7347 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7348 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7349 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7364 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7371 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7391 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7391
  
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
           { FStar_Syntax_Syntax.blob = uu____7410;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7411;
             FStar_Syntax_Syntax.ltyp = uu____7412;
             FStar_Syntax_Syntax.rng = uu____7413;_},uu____7414)
            ->
            let uu____7425 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7425 t21
        | (uu____7426,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7427;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7428;
             FStar_Syntax_Syntax.ltyp = uu____7429;
             FStar_Syntax_Syntax.rng = uu____7430;_})
            ->
            let uu____7441 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7441
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7453 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7453
            then FullMatch
            else
              (let uu____7458 =
                 let uu____7467 =
                   let uu____7470 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7470  in
                 let uu____7471 =
                   let uu____7474 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7474  in
                 (uu____7467, uu____7471)  in
               MisMatch uu____7458)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7480),FStar_Syntax_Syntax.Tm_uinst (g,uu____7482)) ->
            let uu____7491 = head_matches env f g  in
            FStar_All.pipe_right uu____7491 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7492) -> HeadMatch true
        | (uu____7494,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7498 = FStar_Const.eq_const c d  in
            if uu____7498
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7508),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7510)) ->
            let uu____7543 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7543
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7553),FStar_Syntax_Syntax.Tm_refine (y,uu____7555)) ->
            let uu____7564 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7564 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7566),uu____7567) ->
            let uu____7572 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7572 head_match
        | (uu____7573,FStar_Syntax_Syntax.Tm_refine (x,uu____7575)) ->
            let uu____7580 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7580 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7581,FStar_Syntax_Syntax.Tm_type
           uu____7582) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7584,FStar_Syntax_Syntax.Tm_arrow uu____7585) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7616),FStar_Syntax_Syntax.Tm_app (head',uu____7618))
            ->
            let uu____7667 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7667 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7669),uu____7670) ->
            let uu____7695 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7695 head_match
        | (uu____7696,FStar_Syntax_Syntax.Tm_app (head1,uu____7698)) ->
            let uu____7723 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7723 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7724,FStar_Syntax_Syntax.Tm_let
           uu____7725) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7753,FStar_Syntax_Syntax.Tm_match uu____7754) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7800,FStar_Syntax_Syntax.Tm_abs
           uu____7801) -> HeadMatch true
        | uu____7839 ->
            let uu____7844 =
              let uu____7853 = delta_depth_of_term env t11  in
              let uu____7856 = delta_depth_of_term env t21  in
              (uu____7853, uu____7856)  in
            MisMatch uu____7844
  
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
              let uu____7925 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7925  in
            (let uu____7927 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7927
             then
               let uu____7932 = FStar_Syntax_Print.term_to_string t  in
               let uu____7934 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7932 uu____7934
             else ());
            (let uu____7939 =
               let uu____7940 = FStar_Syntax_Util.un_uinst head1  in
               uu____7940.FStar_Syntax_Syntax.n  in
             match uu____7939 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7946 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7946 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7960 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7960
                        then
                          let uu____7965 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7965
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7970 ->
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
                      let uu____7988 =
                        let uu____7990 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____7990 = FStar_Syntax_Util.Equal  in
                      if uu____7988
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7997 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____7997
                          then
                            let uu____8002 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8004 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8002
                              uu____8004
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8009 -> FStar_Pervasives_Native.None)
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
            (let uu____8161 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8161
             then
               let uu____8166 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8168 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8170 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8166
                 uu____8168 uu____8170
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8198 =
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
               match uu____8198 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8246 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8246 with
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
                  uu____8284),uu____8285)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8306 =
                      let uu____8315 = maybe_inline t11  in
                      let uu____8318 = maybe_inline t21  in
                      (uu____8315, uu____8318)  in
                    match uu____8306 with
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
                 (uu____8361,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8362))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8383 =
                      let uu____8392 = maybe_inline t11  in
                      let uu____8395 = maybe_inline t21  in
                      (uu____8392, uu____8395)  in
                    match uu____8383 with
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
             | MisMatch uu____8450 -> fail1 n_delta r t11 t21
             | uu____8459 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8474 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8474
           then
             let uu____8479 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8481 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8483 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8491 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8508 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8508
                    (fun uu____8543  ->
                       match uu____8543 with
                       | (t11,t21) ->
                           let uu____8551 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8553 =
                             let uu____8555 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8555  in
                           Prims.op_Hat uu____8551 uu____8553))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8479 uu____8481 uu____8483 uu____8491
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8572 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8572 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8587  ->
    match uu___24_8587 with
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
      let uu___1213_8636 = p  in
      let uu____8639 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8640 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1213_8636.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8639;
        FStar_TypeChecker_Common.relation =
          (uu___1213_8636.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8640;
        FStar_TypeChecker_Common.element =
          (uu___1213_8636.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1213_8636.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1213_8636.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1213_8636.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1213_8636.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1213_8636.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8655 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8655
            (fun _8660  -> FStar_TypeChecker_Common.TProb _8660)
      | FStar_TypeChecker_Common.CProb uu____8661 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8684 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8684 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8692 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8692 with
           | (lh,lhs_args) ->
               let uu____8739 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8739 with
                | (rh,rhs_args) ->
                    let uu____8786 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8799,FStar_Syntax_Syntax.Tm_uvar uu____8800)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8889 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8916,uu____8917)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8932,FStar_Syntax_Syntax.Tm_uvar uu____8933)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8948,FStar_Syntax_Syntax.Tm_arrow uu____8949)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1264_8979 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1264_8979.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1264_8979.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1264_8979.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1264_8979.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1264_8979.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1264_8979.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1264_8979.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1264_8979.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1264_8979.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8982,FStar_Syntax_Syntax.Tm_type uu____8983)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1264_8999 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1264_8999.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1264_8999.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1264_8999.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1264_8999.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1264_8999.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1264_8999.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1264_8999.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1264_8999.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1264_8999.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9002,FStar_Syntax_Syntax.Tm_uvar uu____9003)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1264_9019 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1264_9019.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1264_9019.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1264_9019.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1264_9019.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1264_9019.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1264_9019.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1264_9019.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1264_9019.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1264_9019.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9022,FStar_Syntax_Syntax.Tm_uvar uu____9023)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9038,uu____9039)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9054,FStar_Syntax_Syntax.Tm_uvar uu____9055)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9070,uu____9071) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8786 with
                     | (rank,tp1) ->
                         let uu____9084 =
                           FStar_All.pipe_right
                             (let uu___1284_9088 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1284_9088.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1284_9088.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1284_9088.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1284_9088.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1284_9088.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1284_9088.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1284_9088.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1284_9088.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1284_9088.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9091  ->
                                FStar_TypeChecker_Common.TProb _9091)
                            in
                         (rank, uu____9084))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9095 =
            FStar_All.pipe_right
              (let uu___1288_9099 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1288_9099.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1288_9099.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1288_9099.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1288_9099.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1288_9099.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1288_9099.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1288_9099.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1288_9099.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1288_9099.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9102  -> FStar_TypeChecker_Common.CProb _9102)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9095)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9162 probs =
      match uu____9162 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9243 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9264 = rank wl.tcenv hd1  in
               (match uu____9264 with
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
                      (let uu____9325 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9330 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9330)
                          in
                       if uu____9325
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
          let uu____9403 = FStar_Syntax_Util.head_and_args t  in
          match uu____9403 with
          | (hd1,uu____9422) ->
              let uu____9447 =
                let uu____9448 = FStar_Syntax_Subst.compress hd1  in
                uu____9448.FStar_Syntax_Syntax.n  in
              (match uu____9447 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9453) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9488  ->
                           match uu____9488 with
                           | (y,uu____9497) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9520  ->
                                       match uu____9520 with
                                       | (x,uu____9529) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9534 -> false)
           in
        let uu____9536 = rank tcenv p  in
        match uu____9536 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9545 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9600 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9619 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9638 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9655 = FStar_Thunk.mkv s  in UFailed uu____9655 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9670 = FStar_Thunk.mk s  in UFailed uu____9670 
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
                        let uu____9722 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9722 with
                        | (k,uu____9730) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9743 -> false)))
            | uu____9745 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9797 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9805 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9805 = Prims.int_zero))
                           in
                        if uu____9797 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9826 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9834 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9834 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9826)
               in
            let uu____9838 = filter1 u12  in
            let uu____9841 = filter1 u22  in (uu____9838, uu____9841)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9876 = filter_out_common_univs us1 us2  in
                   (match uu____9876 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9936 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9936 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9939 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9956  ->
                               let uu____9957 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9959 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9957 uu____9959))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9985 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____9985 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10011 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10011 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10014 ->
                   ufailed_thunk
                     (fun uu____10025  ->
                        let uu____10026 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10028 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10026 uu____10028 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10031,uu____10032) ->
              let uu____10034 =
                let uu____10036 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10038 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10036 uu____10038
                 in
              failwith uu____10034
          | (FStar_Syntax_Syntax.U_unknown ,uu____10041) ->
              let uu____10042 =
                let uu____10044 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10046 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10044 uu____10046
                 in
              failwith uu____10042
          | (uu____10049,FStar_Syntax_Syntax.U_bvar uu____10050) ->
              let uu____10052 =
                let uu____10054 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10056 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10054 uu____10056
                 in
              failwith uu____10052
          | (uu____10059,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10060 =
                let uu____10062 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10064 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10062 uu____10064
                 in
              failwith uu____10060
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10094 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10094
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10111 = occurs_univ v1 u3  in
              if uu____10111
              then
                let uu____10114 =
                  let uu____10116 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10118 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10116 uu____10118
                   in
                try_umax_components u11 u21 uu____10114
              else
                (let uu____10123 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10123)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10135 = occurs_univ v1 u3  in
              if uu____10135
              then
                let uu____10138 =
                  let uu____10140 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10142 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10140 uu____10142
                   in
                try_umax_components u11 u21 uu____10138
              else
                (let uu____10147 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10147)
          | (FStar_Syntax_Syntax.U_max uu____10148,uu____10149) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10157 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10157
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10163,FStar_Syntax_Syntax.U_max uu____10164) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10172 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10172
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10178,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10180,FStar_Syntax_Syntax.U_name uu____10181) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10183) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10185) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10187,FStar_Syntax_Syntax.U_succ uu____10188) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10190,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10297 = bc1  in
      match uu____10297 with
      | (bs1,mk_cod1) ->
          let uu____10341 = bc2  in
          (match uu____10341 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10452 = aux xs ys  in
                     (match uu____10452 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10535 =
                       let uu____10542 = mk_cod1 xs  in ([], uu____10542)  in
                     let uu____10545 =
                       let uu____10552 = mk_cod2 ys  in ([], uu____10552)  in
                     (uu____10535, uu____10545)
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
                  let uu____10621 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10621 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10624 =
                    let uu____10625 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10625 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10624
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10630 = has_type_guard t1 t2  in (uu____10630, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10631 = has_type_guard t2 t1  in (uu____10631, wl)
  
let is_flex_pat :
  'Auu____10641 'Auu____10642 'Auu____10643 .
    ('Auu____10641 * 'Auu____10642 * 'Auu____10643 Prims.list) -> Prims.bool
  =
  fun uu___25_10657  ->
    match uu___25_10657 with
    | (uu____10666,uu____10667,[]) -> true
    | uu____10671 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10704 = f  in
      match uu____10704 with
      | (uu____10711,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10712;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10713;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10716;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10717;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10718;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10719;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10789  ->
                 match uu____10789 with
                 | (y,uu____10798) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10952 =
                  let uu____10967 =
                    let uu____10970 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10970  in
                  ((FStar_List.rev pat_binders), uu____10967)  in
                FStar_Pervasives_Native.Some uu____10952
            | (uu____11003,[]) ->
                let uu____11034 =
                  let uu____11049 =
                    let uu____11052 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11052  in
                  ((FStar_List.rev pat_binders), uu____11049)  in
                FStar_Pervasives_Native.Some uu____11034
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11143 =
                  let uu____11144 = FStar_Syntax_Subst.compress a  in
                  uu____11144.FStar_Syntax_Syntax.n  in
                (match uu____11143 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11164 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11164
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1616_11194 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1616_11194.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1616_11194.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11198 =
                            let uu____11199 =
                              let uu____11206 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11206)  in
                            FStar_Syntax_Syntax.NT uu____11199  in
                          [uu____11198]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1622_11222 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1622_11222.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1622_11222.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11223 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11263 =
                  let uu____11278 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11278  in
                (match uu____11263 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11353 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11386 ->
               let uu____11387 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11387 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11707 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11707
       then
         let uu____11712 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11712
       else ());
      (let uu____11717 = next_prob probs  in
       match uu____11717 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1647_11744 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1647_11744.wl_deferred);
               ctr = (uu___1647_11744.ctr);
               defer_ok = (uu___1647_11744.defer_ok);
               smt_ok = (uu___1647_11744.smt_ok);
               umax_heuristic_ok = (uu___1647_11744.umax_heuristic_ok);
               tcenv = (uu___1647_11744.tcenv);
               wl_implicits = (uu___1647_11744.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11753 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11753
                 then
                   let uu____11756 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11756
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
                       (let uu____11763 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11763)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1659_11769 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1659_11769.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1659_11769.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1659_11769.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1659_11769.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1659_11769.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1659_11769.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1659_11769.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1659_11769.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1659_11769.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11794 ->
                let uu____11804 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11869  ->
                          match uu____11869 with
                          | (c,uu____11879,uu____11880) -> c < probs.ctr))
                   in
                (match uu____11804 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11928 =
                            let uu____11933 =
                              FStar_List.map
                                (fun uu____11954  ->
                                   match uu____11954 with
                                   | (uu____11970,x,y) ->
                                       let uu____11981 = FStar_Thunk.force x
                                          in
                                       (uu____11981, y)) probs.wl_deferred
                               in
                            (uu____11933, (probs.wl_implicits))  in
                          Success uu____11928
                      | uu____11985 ->
                          let uu____11995 =
                            let uu___1677_11996 = probs  in
                            let uu____11997 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12018  ->
                                      match uu____12018 with
                                      | (uu____12026,uu____12027,y) -> y))
                               in
                            {
                              attempting = uu____11997;
                              wl_deferred = rest;
                              ctr = (uu___1677_11996.ctr);
                              defer_ok = (uu___1677_11996.defer_ok);
                              smt_ok = (uu___1677_11996.smt_ok);
                              umax_heuristic_ok =
                                (uu___1677_11996.umax_heuristic_ok);
                              tcenv = (uu___1677_11996.tcenv);
                              wl_implicits = (uu___1677_11996.wl_implicits)
                            }  in
                          solve env uu____11995))))

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
            let uu____12036 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12036 with
            | USolved wl1 ->
                let uu____12038 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12038
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12041 = defer_lit "" orig wl1  in
                solve env uu____12041

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
                  let uu____12092 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12092 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12095 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12108;
                  FStar_Syntax_Syntax.vars = uu____12109;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12112;
                  FStar_Syntax_Syntax.vars = uu____12113;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12126,uu____12127) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12135,FStar_Syntax_Syntax.Tm_uinst uu____12136) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12144 -> USolved wl

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
            ((let uu____12155 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12155
              then
                let uu____12160 = prob_to_string env orig  in
                let uu____12162 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12160 uu____12162
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
               let uu____12255 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12255 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12310 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12310
                then
                  let uu____12315 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12317 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12315 uu____12317
                else ());
               (let uu____12322 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12322 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12368 = eq_prob t1 t2 wl2  in
                         (match uu____12368 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12389 ->
                         let uu____12398 = eq_prob t1 t2 wl2  in
                         (match uu____12398 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12448 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12463 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12464 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12463, uu____12464)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12469 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12470 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12469, uu____12470)
                            in
                         (match uu____12448 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12501 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12501 with
                                | (t1_hd,t1_args) ->
                                    let uu____12546 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12546 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12612 =
                                              let uu____12619 =
                                                let uu____12630 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12630 :: t1_args  in
                                              let uu____12647 =
                                                let uu____12656 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12656 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12705  ->
                                                   fun uu____12706  ->
                                                     fun uu____12707  ->
                                                       match (uu____12705,
                                                               uu____12706,
                                                               uu____12707)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12757),
                                                          (a2,uu____12759))
                                                           ->
                                                           let uu____12796 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12796
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12619
                                                uu____12647
                                               in
                                            match uu____12612 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1831_12822 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1831_12822.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1831_12822.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1831_12822.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12833 =
                                                  solve env1 wl'  in
                                                (match uu____12833 with
                                                 | Success (uu____12836,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1840_12840
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1840_12840.attempting);
                                                            wl_deferred =
                                                              (uu___1840_12840.wl_deferred);
                                                            ctr =
                                                              (uu___1840_12840.ctr);
                                                            defer_ok =
                                                              (uu___1840_12840.defer_ok);
                                                            smt_ok =
                                                              (uu___1840_12840.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1840_12840.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1840_12840.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12841 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12873 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12873 with
                                | (t1_base,p1_opt) ->
                                    let uu____12909 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12909 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13008 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13008
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
                                               let uu____13061 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13061
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
                                               let uu____13093 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13093
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
                                               let uu____13125 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13125
                                           | uu____13128 -> t_base  in
                                         let uu____13145 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13145 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13159 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13159, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13166 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13166 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13202 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13202 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13238 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13238
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
                              let uu____13262 = combine t11 t21 wl2  in
                              (match uu____13262 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13295 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13295
                                     then
                                       let uu____13300 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13300
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13342 ts1 =
               match uu____13342 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13405 = pairwise out t wl2  in
                        (match uu____13405 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13441 =
               let uu____13452 = FStar_List.hd ts  in (uu____13452, [], wl1)
                in
             let uu____13461 = FStar_List.tl ts  in
             aux uu____13441 uu____13461  in
           let uu____13468 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13468 with
           | (this_flex,this_rigid) ->
               let uu____13494 =
                 let uu____13495 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13495.FStar_Syntax_Syntax.n  in
               (match uu____13494 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13520 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13520
                    then
                      let uu____13523 = destruct_flex_t this_flex wl  in
                      (match uu____13523 with
                       | (flex,wl1) ->
                           let uu____13530 = quasi_pattern env flex  in
                           (match uu____13530 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13549 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13549
                                  then
                                    let uu____13554 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13554
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13561 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1942_13564 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1942_13564.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1942_13564.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1942_13564.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1942_13564.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1942_13564.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1942_13564.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1942_13564.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1942_13564.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1942_13564.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13561)
                | uu____13565 ->
                    ((let uu____13567 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13567
                      then
                        let uu____13572 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13572
                      else ());
                     (let uu____13577 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13577 with
                      | (u,_args) ->
                          let uu____13620 =
                            let uu____13621 = FStar_Syntax_Subst.compress u
                               in
                            uu____13621.FStar_Syntax_Syntax.n  in
                          (match uu____13620 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13649 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13649 with
                                 | (u',uu____13668) ->
                                     let uu____13693 =
                                       let uu____13694 = whnf env u'  in
                                       uu____13694.FStar_Syntax_Syntax.n  in
                                     (match uu____13693 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13716 -> false)
                                  in
                               let uu____13718 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13741  ->
                                         match uu___26_13741 with
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
                                              | uu____13755 -> false)
                                         | uu____13759 -> false))
                                  in
                               (match uu____13718 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13774 = whnf env this_rigid
                                         in
                                      let uu____13775 =
                                        FStar_List.collect
                                          (fun uu___27_13781  ->
                                             match uu___27_13781 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13787 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13787]
                                             | uu____13791 -> [])
                                          bounds_probs
                                         in
                                      uu____13774 :: uu____13775  in
                                    let uu____13792 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13792 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13825 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13840 =
                                               let uu____13841 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13841.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13840 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13853 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13853)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13864 -> bound  in
                                           let uu____13865 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13865)  in
                                         (match uu____13825 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13900 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13900
                                                then
                                                  let wl'1 =
                                                    let uu___2002_13906 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2002_13906.wl_deferred);
                                                      ctr =
                                                        (uu___2002_13906.ctr);
                                                      defer_ok =
                                                        (uu___2002_13906.defer_ok);
                                                      smt_ok =
                                                        (uu___2002_13906.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2002_13906.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2002_13906.tcenv);
                                                      wl_implicits =
                                                        (uu___2002_13906.wl_implicits)
                                                    }  in
                                                  let uu____13907 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13907
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13913 =
                                                  solve_t env eq_prob
                                                    (let uu___2007_13915 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2007_13915.wl_deferred);
                                                       ctr =
                                                         (uu___2007_13915.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2007_13915.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2007_13915.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2007_13915.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13913 with
                                                | Success (uu____13917,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2013_13920 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2013_13920.wl_deferred);
                                                        ctr =
                                                          (uu___2013_13920.ctr);
                                                        defer_ok =
                                                          (uu___2013_13920.defer_ok);
                                                        smt_ok =
                                                          (uu___2013_13920.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2013_13920.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2013_13920.tcenv);
                                                        wl_implicits =
                                                          (uu___2013_13920.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2016_13922 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2016_13922.attempting);
                                                        wl_deferred =
                                                          (uu___2016_13922.wl_deferred);
                                                        ctr =
                                                          (uu___2016_13922.ctr);
                                                        defer_ok =
                                                          (uu___2016_13922.defer_ok);
                                                        smt_ok =
                                                          (uu___2016_13922.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2016_13922.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2016_13922.tcenv);
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
                                                    let uu____13938 =
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
                                                    ((let uu____13950 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13950
                                                      then
                                                        let uu____13955 =
                                                          let uu____13957 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13957
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13955
                                                      else ());
                                                     (let uu____13970 =
                                                        let uu____13985 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13985)
                                                         in
                                                      match uu____13970 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14007))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14033 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14033
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
                                                                  let uu____14053
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14053))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14078 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14078
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
                                                                    let uu____14098
                                                                    =
                                                                    let uu____14103
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14103
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14098
                                                                    [] wl2
                                                                     in
                                                                  let uu____14109
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14109))))
                                                      | uu____14110 ->
                                                          let uu____14125 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14125 p)))))))
                           | uu____14132 when flip ->
                               let uu____14133 =
                                 let uu____14135 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14137 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14135 uu____14137
                                  in
                               failwith uu____14133
                           | uu____14140 ->
                               let uu____14141 =
                                 let uu____14143 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14145 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14143 uu____14145
                                  in
                               failwith uu____14141)))))

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
                      (fun uu____14181  ->
                         match uu____14181 with
                         | (x,i) ->
                             let uu____14200 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14200, i)) bs_lhs
                     in
                  let uu____14203 = lhs  in
                  match uu____14203 with
                  | (uu____14204,u_lhs,uu____14206) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14303 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14313 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14313, univ)
                             in
                          match uu____14303 with
                          | (k,univ) ->
                              let uu____14320 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14320 with
                               | (uu____14337,u,wl3) ->
                                   let uu____14340 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14340, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14366 =
                              let uu____14379 =
                                let uu____14390 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14390 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14441  ->
                                   fun uu____14442  ->
                                     match (uu____14441, uu____14442) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14543 =
                                           let uu____14550 =
                                             let uu____14553 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14553
                                              in
                                           copy_uvar u_lhs [] uu____14550 wl2
                                            in
                                         (match uu____14543 with
                                          | (uu____14582,t_a,wl3) ->
                                              let uu____14585 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14585 with
                                               | (uu____14604,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14379
                                ([], wl1)
                               in
                            (match uu____14366 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2127_14660 = ct  in
                                   let uu____14661 =
                                     let uu____14664 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14664
                                      in
                                   let uu____14679 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2127_14660.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2127_14660.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14661;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14679;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2127_14660.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2130_14697 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2130_14697.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2130_14697.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14700 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14700 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14762 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14762 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14773 =
                                          let uu____14778 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14778)  in
                                        TERM uu____14773  in
                                      let uu____14779 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14779 with
                                       | (sub_prob,wl3) ->
                                           let uu____14793 =
                                             let uu____14794 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14794
                                              in
                                           solve env uu____14793))
                             | (x,imp)::formals2 ->
                                 let uu____14816 =
                                   let uu____14823 =
                                     let uu____14826 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14826
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14823 wl1
                                    in
                                 (match uu____14816 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14847 =
                                          let uu____14850 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14850
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14847 u_x
                                         in
                                      let uu____14851 =
                                        let uu____14854 =
                                          let uu____14857 =
                                            let uu____14858 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14858, imp)  in
                                          [uu____14857]  in
                                        FStar_List.append bs_terms
                                          uu____14854
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14851 formals2 wl2)
                              in
                           let uu____14885 = occurs_check u_lhs arrow1  in
                           (match uu____14885 with
                            | (uu____14898,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14914 =
                                    FStar_Thunk.mk
                                      (fun uu____14918  ->
                                         let uu____14919 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14919)
                                     in
                                  giveup_or_defer env orig wl uu____14914
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
              (let uu____14952 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14952
               then
                 let uu____14957 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14960 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14957 (rel_to_string (p_rel orig)) uu____14960
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15091 = rhs wl1 scope env1 subst1  in
                     (match uu____15091 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15114 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15114
                            then
                              let uu____15119 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15119
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15197 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15197 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2200_15199 = hd1  in
                       let uu____15200 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2200_15199.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2200_15199.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15200
                       }  in
                     let hd21 =
                       let uu___2203_15204 = hd2  in
                       let uu____15205 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2203_15204.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2203_15204.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15205
                       }  in
                     let uu____15208 =
                       let uu____15213 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15213
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15208 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15236 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15236
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15243 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15243 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15315 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15315
                                  in
                               ((let uu____15333 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15333
                                 then
                                   let uu____15338 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15340 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15338
                                     uu____15340
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15375 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15411 = aux wl [] env [] bs1 bs2  in
               match uu____15411 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15470 = attempt sub_probs wl2  in
                   solve env1 uu____15470)

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
            let uu___2241_15490 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2241_15490.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2241_15490.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15502 = try_solve env wl'  in
          match uu____15502 with
          | Success (uu____15503,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2250_15507 = wl  in
                  {
                    attempting = (uu___2250_15507.attempting);
                    wl_deferred = (uu___2250_15507.wl_deferred);
                    ctr = (uu___2250_15507.ctr);
                    defer_ok = (uu___2250_15507.defer_ok);
                    smt_ok = (uu___2250_15507.smt_ok);
                    umax_heuristic_ok = (uu___2250_15507.umax_heuristic_ok);
                    tcenv = (uu___2250_15507.tcenv);
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
        (let uu____15516 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15516 wl)

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
              let uu____15530 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15530 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15564 = lhs1  in
              match uu____15564 with
              | (uu____15567,ctx_u,uu____15569) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15577 ->
                        let uu____15578 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15578 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15627 = quasi_pattern env1 lhs1  in
              match uu____15627 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15661) ->
                  let uu____15666 = lhs1  in
                  (match uu____15666 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15681 = occurs_check ctx_u rhs1  in
                       (match uu____15681 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15732 =
                                let uu____15740 =
                                  let uu____15742 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15742
                                   in
                                FStar_Util.Inl uu____15740  in
                              (uu____15732, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15770 =
                                 let uu____15772 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15772  in
                               if uu____15770
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15799 =
                                    let uu____15807 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15807  in
                                  let uu____15813 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15799, uu____15813)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15857 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15857 with
              | (rhs_hd,args) ->
                  let uu____15900 = FStar_Util.prefix args  in
                  (match uu____15900 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15972 = lhs1  in
                       (match uu____15972 with
                        | (t_lhs,u_lhs,lhs_args) ->
                            let uu____15976 =
                              let uu____15983 =
                                let uu____15986 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_left
                                  FStar_Pervasives_Native.fst uu____15986
                                 in
                              copy_uvar u_lhs [] uu____15983 wl1  in
                            (match uu____15976 with
                             | (uu____16009,t_last_arg,wl2) ->
                                 let uu____16012 =
                                   let uu____16019 =
                                     let uu____16022 =
                                       let uu____16031 =
                                         let uu____16040 =
                                           FStar_Syntax_Syntax.null_binder
                                             t_last_arg
                                            in
                                         [uu____16040]  in
                                       FStar_List.append bs_lhs uu____16031
                                        in
                                     let uu____16065 =
                                       FStar_Syntax_Syntax.mk_Total t_res_lhs
                                        in
                                     FStar_Syntax_Util.arrow uu____16022
                                       uu____16065
                                      in
                                   copy_uvar u_lhs [] uu____16019 wl2  in
                                 (match uu____16012 with
                                  | (uu____16074,lhs',wl3) ->
                                      let uu____16077 =
                                        let uu____16084 =
                                          let uu____16087 =
                                            FStar_Syntax_Syntax.mk_Total
                                              t_last_arg
                                             in
                                          FStar_Syntax_Util.arrow bs_lhs
                                            uu____16087
                                           in
                                        copy_uvar u_lhs [] uu____16084 wl3
                                         in
                                      (match uu____16077 with
                                       | (uu____16096,lhs'_last_arg,wl4) ->
                                           let sol =
                                             let uu____16102 =
                                               let uu____16103 =
                                                 let uu____16108 =
                                                   let uu____16109 =
                                                     let uu____16112 =
                                                       let uu____16117 =
                                                         FStar_Syntax_Util.mk_app_binders
                                                           lhs' bs_lhs
                                                          in
                                                       let uu____16118 =
                                                         let uu____16119 =
                                                           let uu____16128 =
                                                             FStar_Syntax_Util.mk_app_binders
                                                               lhs'_last_arg
                                                               bs_lhs
                                                              in
                                                           (uu____16128,
                                                             FStar_Pervasives_Native.None)
                                                            in
                                                         [uu____16119]  in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____16117
                                                         uu____16118
                                                        in
                                                     uu____16112
                                                       FStar_Pervasives_Native.None
                                                       lhs'.FStar_Syntax_Syntax.pos
                                                      in
                                                   FStar_Syntax_Util.abs
                                                     bs_lhs uu____16109
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.residual_tot
                                                           t_res_lhs))
                                                    in
                                                 (u_lhs, uu____16108)  in
                                               TERM uu____16103  in
                                             [uu____16102]  in
                                           let uu____16151 =
                                             let uu____16158 =
                                               let uu____16163 =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   lhs' lhs_args
                                                   FStar_Pervasives_Native.None
                                                   lhs'.FStar_Syntax_Syntax.pos
                                                  in
                                               mk_t_problem wl4 [] orig1
                                                 uu____16163
                                                 FStar_TypeChecker_Common.EQ
                                                 rhs'
                                                 FStar_Pervasives_Native.None
                                                 "first-order lhs"
                                                in
                                             match uu____16158 with
                                             | (p1,wl5) ->
                                                 let uu____16179 =
                                                   let uu____16184 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       lhs'_last_arg lhs_args
                                                       FStar_Pervasives_Native.None
                                                       lhs'_last_arg.FStar_Syntax_Syntax.pos
                                                      in
                                                   mk_t_problem wl5 [] orig1
                                                     uu____16184
                                                     FStar_TypeChecker_Common.EQ
                                                     (FStar_Pervasives_Native.fst
                                                        last_arg_rhs)
                                                     FStar_Pervasives_Native.None
                                                     "first-order rhs"
                                                    in
                                                 (match uu____16179 with
                                                  | (p2,wl6) ->
                                                      ([p1; p2], wl6))
                                              in
                                           (match uu____16151 with
                                            | (sub_probs,wl5) ->
                                                let uu____16212 =
                                                  let uu____16213 =
                                                    solve_prob orig1
                                                      FStar_Pervasives_Native.None
                                                      sol wl5
                                                     in
                                                  attempt sub_probs
                                                    uu____16213
                                                   in
                                                solve env1 uu____16212))))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16247 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16247 with
                | (uu____16265,args) ->
                    (match args with | [] -> false | uu____16301 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16320 =
                  let uu____16321 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16321.FStar_Syntax_Syntax.n  in
                match uu____16320 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16325 -> true
                | uu____16341 -> false  in
              let uu____16343 = quasi_pattern env1 lhs1  in
              match uu____16343 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16361  ->
                         let uu____16362 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16362)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16371 = is_app rhs1  in
                  if uu____16371
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16376 = is_arrow rhs1  in
                     if uu____16376
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16388  ->
                               let uu____16389 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16389)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16393 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16393
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16399 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16399
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16404 = lhs  in
                (match uu____16404 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16408 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16408 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16426 =
                              let uu____16430 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16430
                               in
                            FStar_All.pipe_right uu____16426
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16451 = occurs_check ctx_uv rhs1  in
                          (match uu____16451 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16480 =
                                   let uu____16481 =
                                     let uu____16483 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16483
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16481
                                    in
                                 giveup_or_defer env orig wl uu____16480
                               else
                                 (let uu____16491 =
                                    (FStar_Util.set_is_subset_of fvs2 fvs1)
                                      &&
                                      (tgt_ctx_includes_all_source_ctx ctx_uv
                                         uvars1)
                                     in
                                  if uu____16491
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let uu____16497 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl
                                       in
                                    solve env uu____16497
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16510  ->
                                              let uu____16511 =
                                                names_to_string1 fvs2  in
                                              let uu____16513 =
                                                names_to_string1 fvs1  in
                                              let uu____16515 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16511 uu____16513
                                                uu____16515)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16527 ->
                          if wl.defer_ok
                          then
                            let uu____16531 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16531
                          else
                            (let uu____16536 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16536 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16562 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16562
                             | (FStar_Util.Inl msg,uu____16564) ->
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
                  let uu____16582 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16582
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16588 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16588
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16610 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16610
                else
                  (let uu____16615 =
                     let uu____16632 = quasi_pattern env lhs  in
                     let uu____16639 = quasi_pattern env rhs  in
                     (uu____16632, uu____16639)  in
                   match uu____16615 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16682 = lhs  in
                       (match uu____16682 with
                        | ({ FStar_Syntax_Syntax.n = uu____16683;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16685;_},u_lhs,uu____16687)
                            ->
                            let uu____16690 = rhs  in
                            (match uu____16690 with
                             | (uu____16691,u_rhs,uu____16693) ->
                                 let uu____16694 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16694
                                 then
                                   let uu____16701 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16701
                                 else
                                   (let uu____16704 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16704 with
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
                                        let uu____16736 =
                                          let uu____16743 =
                                            let uu____16746 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16746
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16743
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16736 with
                                         | (uu____16758,w,wl1) ->
                                             let w_app =
                                               let uu____16764 =
                                                 let uu____16769 =
                                                   FStar_List.map
                                                     (fun uu____16780  ->
                                                        match uu____16780
                                                        with
                                                        | (z,uu____16788) ->
                                                            let uu____16793 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16793) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16769
                                                  in
                                               uu____16764
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16795 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16795
                                               then
                                                 let uu____16800 =
                                                   let uu____16804 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16806 =
                                                     let uu____16810 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16812 =
                                                       let uu____16816 =
                                                         term_to_string w  in
                                                       let uu____16818 =
                                                         let uu____16822 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16831 =
                                                           let uu____16835 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16844 =
                                                             let uu____16848
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16848]
                                                              in
                                                           uu____16835 ::
                                                             uu____16844
                                                            in
                                                         uu____16822 ::
                                                           uu____16831
                                                          in
                                                       uu____16816 ::
                                                         uu____16818
                                                        in
                                                     uu____16810 ::
                                                       uu____16812
                                                      in
                                                   uu____16804 :: uu____16806
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16800
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16865 =
                                                     let uu____16870 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16870)  in
                                                   TERM uu____16865  in
                                                 let uu____16871 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16871
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16879 =
                                                        let uu____16884 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16884)
                                                         in
                                                      TERM uu____16879  in
                                                    [s1; s2])
                                                  in
                                               let uu____16885 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16885))))))
                   | uu____16886 ->
                       let uu____16903 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16903)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16957 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16957
            then
              let uu____16962 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16964 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16966 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16968 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16962 uu____16964 uu____16966 uu____16968
            else ());
           (let uu____16979 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16979 with
            | (head1,args1) ->
                let uu____17022 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17022 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17092 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17092 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17097 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17097)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17118 =
                         FStar_Thunk.mk
                           (fun uu____17125  ->
                              let uu____17126 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17128 = args_to_string args1  in
                              let uu____17132 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17134 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17126 uu____17128 uu____17132
                                uu____17134)
                          in
                       giveup env1 uu____17118 orig
                     else
                       (let uu____17141 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17146 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17146 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17141
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2501_17150 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2501_17150.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2501_17150.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2501_17150.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2501_17150.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2501_17150.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2501_17150.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2501_17150.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2501_17150.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17160 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17160
                                    else solve env1 wl2))
                        else
                          (let uu____17165 = base_and_refinement env1 t1  in
                           match uu____17165 with
                           | (base1,refinement1) ->
                               let uu____17190 = base_and_refinement env1 t2
                                  in
                               (match uu____17190 with
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
                                           let uu____17355 =
                                             FStar_List.fold_right
                                               (fun uu____17395  ->
                                                  fun uu____17396  ->
                                                    match (uu____17395,
                                                            uu____17396)
                                                    with
                                                    | (((a1,uu____17448),
                                                        (a2,uu____17450)),
                                                       (probs,wl3)) ->
                                                        let uu____17499 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17499
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17355 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17542 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17542
                                                 then
                                                   let uu____17547 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17547
                                                 else ());
                                                (let uu____17553 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17553
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
                                                    (let uu____17580 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17580 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17596 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17596
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17604 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17604))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17629 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17629 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17645 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17645
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17653 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17653)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17681 =
                                           match uu____17681 with
                                           | (prob,reason) ->
                                               ((let uu____17698 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17698
                                                 then
                                                   let uu____17703 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17705 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17707 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17703 uu____17705
                                                     uu____17707
                                                 else ());
                                                (let uu____17713 =
                                                   let uu____17722 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17725 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17722, uu____17725)
                                                    in
                                                 match uu____17713 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17738 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17738 with
                                                      | (head1',uu____17756)
                                                          ->
                                                          let uu____17781 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17781
                                                           with
                                                           | (head2',uu____17799)
                                                               ->
                                                               let uu____17824
                                                                 =
                                                                 let uu____17829
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17830
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17829,
                                                                   uu____17830)
                                                                  in
                                                               (match uu____17824
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17832
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17832
                                                                    then
                                                                    let uu____17837
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17839
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17841
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17843
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17837
                                                                    uu____17839
                                                                    uu____17841
                                                                    uu____17843
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17848
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2589_17856
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2589_17856.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17858
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17858
                                                                    then
                                                                    let uu____17863
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17863
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17868 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17880 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17880 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17888 =
                                             let uu____17889 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17889.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17888 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17894 -> false  in
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
                                          | uu____17897 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17900 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2609_17936 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2609_17936.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2609_17936.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2609_17936.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2609_17936.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2609_17936.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2609_17936.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2609_17936.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2609_17936.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18012 = destruct_flex_t scrutinee wl1  in
             match uu____18012 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18023 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18023 with
                  | (xs,pat_term,uu____18039,uu____18040) ->
                      let uu____18045 =
                        FStar_List.fold_left
                          (fun uu____18068  ->
                             fun x  ->
                               match uu____18068 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18089 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18089 with
                                    | (uu____18108,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18045 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18129 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18129 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2649_18146 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2649_18146.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2649_18146.umax_heuristic_ok);
                                    tcenv = (uu___2649_18146.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18157 = solve env1 wl'  in
                                (match uu____18157 with
                                 | Success (uu____18160,imps) ->
                                     let wl'1 =
                                       let uu___2657_18163 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2657_18163.wl_deferred);
                                         ctr = (uu___2657_18163.ctr);
                                         defer_ok =
                                           (uu___2657_18163.defer_ok);
                                         smt_ok = (uu___2657_18163.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2657_18163.umax_heuristic_ok);
                                         tcenv = (uu___2657_18163.tcenv);
                                         wl_implicits =
                                           (uu___2657_18163.wl_implicits)
                                       }  in
                                     let uu____18164 = solve env1 wl'1  in
                                     (match uu____18164 with
                                      | Success (uu____18167,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2665_18171 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2665_18171.attempting);
                                                 wl_deferred =
                                                   (uu___2665_18171.wl_deferred);
                                                 ctr = (uu___2665_18171.ctr);
                                                 defer_ok =
                                                   (uu___2665_18171.defer_ok);
                                                 smt_ok =
                                                   (uu___2665_18171.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2665_18171.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2665_18171.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18172 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18178 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18201 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18201
                 then
                   let uu____18206 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18208 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18206 uu____18208
                 else ());
                (let uu____18213 =
                   let uu____18234 =
                     let uu____18243 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18243)  in
                   let uu____18250 =
                     let uu____18259 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18259)  in
                   (uu____18234, uu____18250)  in
                 match uu____18213 with
                 | ((uu____18289,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18292;
                                   FStar_Syntax_Syntax.vars = uu____18293;_}),
                    (s,t)) ->
                     let uu____18364 =
                       let uu____18366 = is_flex scrutinee  in
                       Prims.op_Negation uu____18366  in
                     if uu____18364
                     then
                       ((let uu____18377 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18377
                         then
                           let uu____18382 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18382
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18401 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18401
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18416 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18416
                           then
                             let uu____18421 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18423 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18421 uu____18423
                           else ());
                          (let pat_discriminates uu___28_18448 =
                             match uu___28_18448 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18464;
                                  FStar_Syntax_Syntax.p = uu____18465;_},FStar_Pervasives_Native.None
                                ,uu____18466) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18480;
                                  FStar_Syntax_Syntax.p = uu____18481;_},FStar_Pervasives_Native.None
                                ,uu____18482) -> true
                             | uu____18509 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18612 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18612 with
                                       | (uu____18614,uu____18615,t') ->
                                           let uu____18633 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18633 with
                                            | (FullMatch ,uu____18645) ->
                                                true
                                            | (HeadMatch
                                               uu____18659,uu____18660) ->
                                                true
                                            | uu____18675 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18712 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18712
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18723 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18723 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18811,uu____18812) ->
                                       branches1
                                   | uu____18957 -> branches  in
                                 let uu____19012 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19021 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19021 with
                                        | (p,uu____19025,uu____19026) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19055  -> FStar_Util.Inr _19055)
                                   uu____19012))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19085 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19085 with
                                | (p,uu____19094,e) ->
                                    ((let uu____19113 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19113
                                      then
                                        let uu____19118 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19120 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19118 uu____19120
                                      else ());
                                     (let uu____19125 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19140  -> FStar_Util.Inr _19140)
                                        uu____19125)))))
                 | ((s,t),(uu____19143,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19146;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19147;_}))
                     ->
                     let uu____19216 =
                       let uu____19218 = is_flex scrutinee  in
                       Prims.op_Negation uu____19218  in
                     if uu____19216
                     then
                       ((let uu____19229 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19229
                         then
                           let uu____19234 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19234
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19253 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19253
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19268 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19268
                           then
                             let uu____19273 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19275 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19273 uu____19275
                           else ());
                          (let pat_discriminates uu___28_19300 =
                             match uu___28_19300 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19316;
                                  FStar_Syntax_Syntax.p = uu____19317;_},FStar_Pervasives_Native.None
                                ,uu____19318) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19332;
                                  FStar_Syntax_Syntax.p = uu____19333;_},FStar_Pervasives_Native.None
                                ,uu____19334) -> true
                             | uu____19361 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19464 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19464 with
                                       | (uu____19466,uu____19467,t') ->
                                           let uu____19485 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19485 with
                                            | (FullMatch ,uu____19497) ->
                                                true
                                            | (HeadMatch
                                               uu____19511,uu____19512) ->
                                                true
                                            | uu____19527 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19564 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19564
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19575 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19575 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19663,uu____19664) ->
                                       branches1
                                   | uu____19809 -> branches  in
                                 let uu____19864 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19873 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19873 with
                                        | (p,uu____19877,uu____19878) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19907  -> FStar_Util.Inr _19907)
                                   uu____19864))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19937 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19937 with
                                | (p,uu____19946,e) ->
                                    ((let uu____19965 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19965
                                      then
                                        let uu____19970 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19972 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19970 uu____19972
                                      else ());
                                     (let uu____19977 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19992  -> FStar_Util.Inr _19992)
                                        uu____19977)))))
                 | uu____19993 ->
                     ((let uu____20015 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20015
                       then
                         let uu____20020 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20022 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20020 uu____20022
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20068 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20068
            then
              let uu____20073 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20075 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20077 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20079 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20073 uu____20075 uu____20077 uu____20079
            else ());
           (let uu____20084 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20084 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20115,uu____20116) ->
                     let rec may_relate head3 =
                       let uu____20144 =
                         let uu____20145 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20145.FStar_Syntax_Syntax.n  in
                       match uu____20144 with
                       | FStar_Syntax_Syntax.Tm_name uu____20149 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20151 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20176 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20176 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20178 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20181
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20182 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20185,uu____20186) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20228) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20234) ->
                           may_relate t
                       | uu____20239 -> false  in
                     let uu____20241 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20241 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20254 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20254
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20264 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20264
                          then
                            let uu____20267 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20267 with
                             | (guard,wl2) ->
                                 let uu____20274 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20274)
                          else
                            (let uu____20277 =
                               FStar_Thunk.mk
                                 (fun uu____20284  ->
                                    let uu____20285 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20287 =
                                      let uu____20289 =
                                        let uu____20293 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20293
                                          (fun x  ->
                                             let uu____20300 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20300)
                                         in
                                      FStar_Util.dflt "" uu____20289  in
                                    let uu____20305 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20307 =
                                      let uu____20309 =
                                        let uu____20313 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20313
                                          (fun x  ->
                                             let uu____20320 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20320)
                                         in
                                      FStar_Util.dflt "" uu____20309  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20285 uu____20287 uu____20305
                                      uu____20307)
                                in
                             giveup env1 uu____20277 orig))
                 | (HeadMatch (true ),uu____20326) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20341 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20341 with
                        | (guard,wl2) ->
                            let uu____20348 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20348)
                     else
                       (let uu____20351 =
                          FStar_Thunk.mk
                            (fun uu____20356  ->
                               let uu____20357 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20359 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20357 uu____20359)
                           in
                        giveup env1 uu____20351 orig)
                 | (uu____20362,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2840_20376 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2840_20376.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2840_20376.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2840_20376.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2840_20376.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2840_20376.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2840_20376.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2840_20376.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2840_20376.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20403 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20403
          then
            let uu____20406 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20406
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20412 =
                let uu____20415 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20415  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20412 t1);
             (let uu____20434 =
                let uu____20437 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20437  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20434 t2);
             (let uu____20456 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20456
              then
                let uu____20460 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20462 =
                  let uu____20464 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20466 =
                    let uu____20468 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20468  in
                  Prims.op_Hat uu____20464 uu____20466  in
                let uu____20471 =
                  let uu____20473 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20475 =
                    let uu____20477 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20477  in
                  Prims.op_Hat uu____20473 uu____20475  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20460 uu____20462 uu____20471
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20484,uu____20485) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20509,FStar_Syntax_Syntax.Tm_delayed uu____20510) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20534,uu____20535) ->
                  let uu____20562 =
                    let uu___2871_20563 = problem  in
                    let uu____20564 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2871_20563.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20564;
                      FStar_TypeChecker_Common.relation =
                        (uu___2871_20563.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2871_20563.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2871_20563.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2871_20563.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2871_20563.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2871_20563.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2871_20563.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2871_20563.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20562 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20565,uu____20566) ->
                  let uu____20573 =
                    let uu___2877_20574 = problem  in
                    let uu____20575 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2877_20574.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20575;
                      FStar_TypeChecker_Common.relation =
                        (uu___2877_20574.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2877_20574.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2877_20574.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2877_20574.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2877_20574.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2877_20574.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2877_20574.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2877_20574.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20573 wl
              | (uu____20576,FStar_Syntax_Syntax.Tm_ascribed uu____20577) ->
                  let uu____20604 =
                    let uu___2883_20605 = problem  in
                    let uu____20606 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2883_20605.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2883_20605.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2883_20605.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20606;
                      FStar_TypeChecker_Common.element =
                        (uu___2883_20605.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2883_20605.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2883_20605.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2883_20605.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2883_20605.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2883_20605.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20604 wl
              | (uu____20607,FStar_Syntax_Syntax.Tm_meta uu____20608) ->
                  let uu____20615 =
                    let uu___2889_20616 = problem  in
                    let uu____20617 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2889_20616.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2889_20616.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2889_20616.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20617;
                      FStar_TypeChecker_Common.element =
                        (uu___2889_20616.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2889_20616.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2889_20616.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2889_20616.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2889_20616.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2889_20616.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20615 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20619),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20621)) ->
                  let uu____20630 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20630
              | (FStar_Syntax_Syntax.Tm_bvar uu____20631,uu____20632) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20634,FStar_Syntax_Syntax.Tm_bvar uu____20635) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20705 =
                    match uu___29_20705 with
                    | [] -> c
                    | bs ->
                        let uu____20733 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20733
                     in
                  let uu____20744 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20744 with
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
                                    let uu____20893 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20893
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
                  let mk_t t l uu___30_20982 =
                    match uu___30_20982 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21024 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21024 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21169 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21170 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21169
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21170 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21172,uu____21173) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21204 -> true
                    | uu____21224 -> false  in
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
                      (let uu____21284 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2991_21292 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2991_21292.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2991_21292.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2991_21292.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2991_21292.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2991_21292.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2991_21292.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2991_21292.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2991_21292.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2991_21292.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2991_21292.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2991_21292.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2991_21292.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2991_21292.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2991_21292.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2991_21292.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2991_21292.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2991_21292.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2991_21292.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2991_21292.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2991_21292.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2991_21292.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2991_21292.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2991_21292.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2991_21292.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2991_21292.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2991_21292.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2991_21292.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2991_21292.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2991_21292.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2991_21292.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2991_21292.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2991_21292.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2991_21292.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2991_21292.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2991_21292.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2991_21292.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2991_21292.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2991_21292.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2991_21292.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2991_21292.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2991_21292.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2991_21292.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2991_21292.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2991_21292.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21284 with
                       | (uu____21297,ty,uu____21299) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21308 =
                                 let uu____21309 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21309.FStar_Syntax_Syntax.n  in
                               match uu____21308 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21312 ->
                                   let uu____21319 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21319
                               | uu____21320 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21323 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21323
                             then
                               let uu____21328 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21330 =
                                 let uu____21332 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21332
                                  in
                               let uu____21333 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21328 uu____21330 uu____21333
                             else ());
                            r1))
                     in
                  let uu____21338 =
                    let uu____21355 = maybe_eta t1  in
                    let uu____21362 = maybe_eta t2  in
                    (uu____21355, uu____21362)  in
                  (match uu____21338 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3012_21404 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3012_21404.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3012_21404.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3012_21404.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3012_21404.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3012_21404.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3012_21404.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3012_21404.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3012_21404.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21425 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21425
                       then
                         let uu____21428 = destruct_flex_t not_abs wl  in
                         (match uu____21428 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3029_21445 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3029_21445.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3029_21445.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3029_21445.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3029_21445.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3029_21445.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3029_21445.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3029_21445.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3029_21445.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21448 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21448 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21471 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21471
                       then
                         let uu____21474 = destruct_flex_t not_abs wl  in
                         (match uu____21474 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3029_21491 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3029_21491.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3029_21491.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3029_21491.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3029_21491.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3029_21491.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3029_21491.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3029_21491.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3029_21491.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21494 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21494 orig))
                   | uu____21497 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21515,FStar_Syntax_Syntax.Tm_abs uu____21516) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21547 -> true
                    | uu____21567 -> false  in
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
                      (let uu____21627 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___2991_21635 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___2991_21635.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___2991_21635.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___2991_21635.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___2991_21635.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___2991_21635.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___2991_21635.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___2991_21635.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___2991_21635.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___2991_21635.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___2991_21635.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___2991_21635.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___2991_21635.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___2991_21635.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___2991_21635.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___2991_21635.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___2991_21635.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___2991_21635.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___2991_21635.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___2991_21635.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___2991_21635.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___2991_21635.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___2991_21635.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___2991_21635.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___2991_21635.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___2991_21635.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___2991_21635.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___2991_21635.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___2991_21635.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___2991_21635.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___2991_21635.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___2991_21635.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___2991_21635.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___2991_21635.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___2991_21635.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___2991_21635.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___2991_21635.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___2991_21635.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___2991_21635.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___2991_21635.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___2991_21635.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___2991_21635.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___2991_21635.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___2991_21635.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___2991_21635.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21627 with
                       | (uu____21640,ty,uu____21642) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21651 =
                                 let uu____21652 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21652.FStar_Syntax_Syntax.n  in
                               match uu____21651 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21655 ->
                                   let uu____21662 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21662
                               | uu____21663 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21666 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21666
                             then
                               let uu____21671 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21673 =
                                 let uu____21675 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21675
                                  in
                               let uu____21676 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21671 uu____21673 uu____21676
                             else ());
                            r1))
                     in
                  let uu____21681 =
                    let uu____21698 = maybe_eta t1  in
                    let uu____21705 = maybe_eta t2  in
                    (uu____21698, uu____21705)  in
                  (match uu____21681 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3012_21747 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3012_21747.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3012_21747.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3012_21747.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3012_21747.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3012_21747.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3012_21747.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3012_21747.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3012_21747.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21768 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21768
                       then
                         let uu____21771 = destruct_flex_t not_abs wl  in
                         (match uu____21771 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3029_21788 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3029_21788.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3029_21788.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3029_21788.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3029_21788.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3029_21788.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3029_21788.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3029_21788.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3029_21788.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21791 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21791 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21814 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21814
                       then
                         let uu____21817 = destruct_flex_t not_abs wl  in
                         (match uu____21817 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3029_21834 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3029_21834.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3029_21834.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3029_21834.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3029_21834.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3029_21834.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3029_21834.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3029_21834.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3029_21834.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21837 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21837 orig))
                   | uu____21840 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21870 =
                    let uu____21875 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21875 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3052_21903 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3052_21903.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3052_21903.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3054_21905 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3054_21905.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3054_21905.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21906,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3052_21921 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3052_21921.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3052_21921.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3054_21923 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3054_21923.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3054_21923.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21924 -> (x1, x2)  in
                  (match uu____21870 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21943 = as_refinement false env t11  in
                       (match uu____21943 with
                        | (x12,phi11) ->
                            let uu____21951 = as_refinement false env t21  in
                            (match uu____21951 with
                             | (x22,phi21) ->
                                 ((let uu____21960 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21960
                                   then
                                     ((let uu____21965 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21967 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21969 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21965
                                         uu____21967 uu____21969);
                                      (let uu____21972 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21974 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21976 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21972
                                         uu____21974 uu____21976))
                                   else ());
                                  (let uu____21981 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21981 with
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
                                         let uu____22052 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22052
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22064 =
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
                                         (let uu____22077 =
                                            let uu____22080 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22080
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22077
                                            (p_guard base_prob));
                                         (let uu____22099 =
                                            let uu____22102 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22102
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22099
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22121 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22121)
                                          in
                                       let has_uvars =
                                         (let uu____22126 =
                                            let uu____22128 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22128
                                             in
                                          Prims.op_Negation uu____22126) ||
                                           (let uu____22132 =
                                              let uu____22134 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22134
                                               in
                                            Prims.op_Negation uu____22132)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22138 =
                                           let uu____22143 =
                                             let uu____22152 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22152]  in
                                           mk_t_problem wl1 uu____22143 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22138 with
                                          | (ref_prob,wl2) ->
                                              let uu____22174 =
                                                solve env1
                                                  (let uu___3096_22176 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3096_22176.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3096_22176.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3096_22176.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3096_22176.tcenv);
                                                     wl_implicits =
                                                       (uu___3096_22176.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22174 with
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
                                               | Success uu____22190 ->
                                                   let guard =
                                                     let uu____22198 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22198
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3107_22207 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3107_22207.attempting);
                                                       wl_deferred =
                                                         (uu___3107_22207.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3107_22207.defer_ok);
                                                       smt_ok =
                                                         (uu___3107_22207.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3107_22207.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3107_22207.tcenv);
                                                       wl_implicits =
                                                         (uu___3107_22207.wl_implicits)
                                                     }  in
                                                   let uu____22209 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22209))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22212,FStar_Syntax_Syntax.Tm_uvar uu____22213) ->
                  let uu____22238 = destruct_flex_t t1 wl  in
                  (match uu____22238 with
                   | (f1,wl1) ->
                       let uu____22245 = destruct_flex_t t2 wl1  in
                       (match uu____22245 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22252;
                    FStar_Syntax_Syntax.pos = uu____22253;
                    FStar_Syntax_Syntax.vars = uu____22254;_},uu____22255),FStar_Syntax_Syntax.Tm_uvar
                 uu____22256) ->
                  let uu____22305 = destruct_flex_t t1 wl  in
                  (match uu____22305 with
                   | (f1,wl1) ->
                       let uu____22312 = destruct_flex_t t2 wl1  in
                       (match uu____22312 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22319,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22320;
                    FStar_Syntax_Syntax.pos = uu____22321;
                    FStar_Syntax_Syntax.vars = uu____22322;_},uu____22323))
                  ->
                  let uu____22372 = destruct_flex_t t1 wl  in
                  (match uu____22372 with
                   | (f1,wl1) ->
                       let uu____22379 = destruct_flex_t t2 wl1  in
                       (match uu____22379 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22386;
                    FStar_Syntax_Syntax.pos = uu____22387;
                    FStar_Syntax_Syntax.vars = uu____22388;_},uu____22389),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22390;
                    FStar_Syntax_Syntax.pos = uu____22391;
                    FStar_Syntax_Syntax.vars = uu____22392;_},uu____22393))
                  ->
                  let uu____22466 = destruct_flex_t t1 wl  in
                  (match uu____22466 with
                   | (f1,wl1) ->
                       let uu____22473 = destruct_flex_t t2 wl1  in
                       (match uu____22473 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22480,uu____22481) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22494 = destruct_flex_t t1 wl  in
                  (match uu____22494 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22501;
                    FStar_Syntax_Syntax.pos = uu____22502;
                    FStar_Syntax_Syntax.vars = uu____22503;_},uu____22504),uu____22505)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22542 = destruct_flex_t t1 wl  in
                  (match uu____22542 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22549,FStar_Syntax_Syntax.Tm_uvar uu____22550) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22563,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22564;
                    FStar_Syntax_Syntax.pos = uu____22565;
                    FStar_Syntax_Syntax.vars = uu____22566;_},uu____22567))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22604,FStar_Syntax_Syntax.Tm_arrow uu____22605) ->
                  solve_t' env
                    (let uu___3207_22633 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3207_22633.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3207_22633.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3207_22633.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3207_22633.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3207_22633.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3207_22633.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3207_22633.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3207_22633.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3207_22633.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22634;
                    FStar_Syntax_Syntax.pos = uu____22635;
                    FStar_Syntax_Syntax.vars = uu____22636;_},uu____22637),FStar_Syntax_Syntax.Tm_arrow
                 uu____22638) ->
                  solve_t' env
                    (let uu___3207_22690 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3207_22690.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3207_22690.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3207_22690.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3207_22690.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3207_22690.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3207_22690.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3207_22690.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3207_22690.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3207_22690.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22691,FStar_Syntax_Syntax.Tm_uvar uu____22692) ->
                  let uu____22705 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22705
              | (uu____22706,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22707;
                    FStar_Syntax_Syntax.pos = uu____22708;
                    FStar_Syntax_Syntax.vars = uu____22709;_},uu____22710))
                  ->
                  let uu____22747 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22747
              | (FStar_Syntax_Syntax.Tm_uvar uu____22748,uu____22749) ->
                  let uu____22762 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22762
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22763;
                    FStar_Syntax_Syntax.pos = uu____22764;
                    FStar_Syntax_Syntax.vars = uu____22765;_},uu____22766),uu____22767)
                  ->
                  let uu____22804 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22804
              | (FStar_Syntax_Syntax.Tm_refine uu____22805,uu____22806) ->
                  let t21 =
                    let uu____22814 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22814  in
                  solve_t env
                    (let uu___3242_22840 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3242_22840.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3242_22840.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3242_22840.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3242_22840.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3242_22840.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3242_22840.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3242_22840.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3242_22840.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3242_22840.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22841,FStar_Syntax_Syntax.Tm_refine uu____22842) ->
                  let t11 =
                    let uu____22850 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22850  in
                  solve_t env
                    (let uu___3249_22876 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3249_22876.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3249_22876.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3249_22876.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3249_22876.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3249_22876.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3249_22876.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3249_22876.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3249_22876.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3249_22876.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22958 =
                    let uu____22959 = guard_of_prob env wl problem t1 t2  in
                    match uu____22959 with
                    | (guard,wl1) ->
                        let uu____22966 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22966
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23185 = br1  in
                        (match uu____23185 with
                         | (p1,w1,uu____23214) ->
                             let uu____23231 = br2  in
                             (match uu____23231 with
                              | (p2,w2,uu____23254) ->
                                  let uu____23259 =
                                    let uu____23261 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23261  in
                                  if uu____23259
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23288 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23288 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23325 = br2  in
                                         (match uu____23325 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23358 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23358
                                                 in
                                              let uu____23363 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23394,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23415) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23474 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23474 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23363
                                                (fun uu____23546  ->
                                                   match uu____23546 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23583 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23583
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23604
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23604
                                                              then
                                                                let uu____23609
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23611
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23609
                                                                  uu____23611
                                                              else ());
                                                             (let uu____23617
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23617
                                                                (fun
                                                                   uu____23653
                                                                    ->
                                                                   match uu____23653
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
                    | uu____23782 -> FStar_Pervasives_Native.None  in
                  let uu____23823 = solve_branches wl brs1 brs2  in
                  (match uu____23823 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23849 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23849 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23876 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23876 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23910 =
                                FStar_List.map
                                  (fun uu____23922  ->
                                     match uu____23922 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23910  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23931 =
                              let uu____23932 =
                                let uu____23933 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23933
                                  (let uu___3348_23941 = wl3  in
                                   {
                                     attempting =
                                       (uu___3348_23941.attempting);
                                     wl_deferred =
                                       (uu___3348_23941.wl_deferred);
                                     ctr = (uu___3348_23941.ctr);
                                     defer_ok = (uu___3348_23941.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3348_23941.umax_heuristic_ok);
                                     tcenv = (uu___3348_23941.tcenv);
                                     wl_implicits =
                                       (uu___3348_23941.wl_implicits)
                                   })
                                 in
                              solve env uu____23932  in
                            (match uu____23931 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23946 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23955 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23955 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23958,uu____23959) ->
                  let head1 =
                    let uu____23983 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23983
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24029 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24029
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24075 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24075
                    then
                      let uu____24079 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24081 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24083 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24079 uu____24081 uu____24083
                    else ());
                   (let no_free_uvars t =
                      (let uu____24097 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24097) &&
                        (let uu____24101 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24101)
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
                      let uu____24120 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24120 = FStar_Syntax_Util.Equal  in
                    let uu____24121 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24121
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24125 = equal t1 t2  in
                         (if uu____24125
                          then
                            let uu____24128 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24128
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24133 =
                            let uu____24140 = equal t1 t2  in
                            if uu____24140
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24153 = mk_eq2 wl env orig t1 t2  in
                               match uu____24153 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24133 with
                          | (guard,wl1) ->
                              let uu____24174 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24174))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24177,uu____24178) ->
                  let head1 =
                    let uu____24186 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24186
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24232 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24232
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24278 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24278
                    then
                      let uu____24282 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24284 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24286 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24282 uu____24284 uu____24286
                    else ());
                   (let no_free_uvars t =
                      (let uu____24300 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24300) &&
                        (let uu____24304 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24304)
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
                      let uu____24323 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24323 = FStar_Syntax_Util.Equal  in
                    let uu____24324 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24324
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24328 = equal t1 t2  in
                         (if uu____24328
                          then
                            let uu____24331 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24331
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24336 =
                            let uu____24343 = equal t1 t2  in
                            if uu____24343
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24356 = mk_eq2 wl env orig t1 t2  in
                               match uu____24356 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24336 with
                          | (guard,wl1) ->
                              let uu____24377 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24377))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24380,uu____24381) ->
                  let head1 =
                    let uu____24383 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24383
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24429 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24429
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24475 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24475
                    then
                      let uu____24479 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24481 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24483 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24479 uu____24481 uu____24483
                    else ());
                   (let no_free_uvars t =
                      (let uu____24497 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24497) &&
                        (let uu____24501 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24501)
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
                      let uu____24520 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24520 = FStar_Syntax_Util.Equal  in
                    let uu____24521 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24521
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24525 = equal t1 t2  in
                         (if uu____24525
                          then
                            let uu____24528 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24528
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24533 =
                            let uu____24540 = equal t1 t2  in
                            if uu____24540
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24553 = mk_eq2 wl env orig t1 t2  in
                               match uu____24553 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24533 with
                          | (guard,wl1) ->
                              let uu____24574 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24574))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24577,uu____24578) ->
                  let head1 =
                    let uu____24580 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24580
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24626 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24626
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24672 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24672
                    then
                      let uu____24676 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24678 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24680 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24676 uu____24678 uu____24680
                    else ());
                   (let no_free_uvars t =
                      (let uu____24694 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24694) &&
                        (let uu____24698 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24698)
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
                      let uu____24717 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24717 = FStar_Syntax_Util.Equal  in
                    let uu____24718 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24718
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24722 = equal t1 t2  in
                         (if uu____24722
                          then
                            let uu____24725 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24725
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24730 =
                            let uu____24737 = equal t1 t2  in
                            if uu____24737
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24750 = mk_eq2 wl env orig t1 t2  in
                               match uu____24750 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24730 with
                          | (guard,wl1) ->
                              let uu____24771 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24771))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24774,uu____24775) ->
                  let head1 =
                    let uu____24777 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24777
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24823 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24823
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24869 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24869
                    then
                      let uu____24873 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24875 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24877 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24873 uu____24875 uu____24877
                    else ());
                   (let no_free_uvars t =
                      (let uu____24891 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24891) &&
                        (let uu____24895 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24895)
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
                      let uu____24914 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24914 = FStar_Syntax_Util.Equal  in
                    let uu____24915 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24915
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24919 = equal t1 t2  in
                         (if uu____24919
                          then
                            let uu____24922 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24922
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24927 =
                            let uu____24934 = equal t1 t2  in
                            if uu____24934
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24947 = mk_eq2 wl env orig t1 t2  in
                               match uu____24947 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24927 with
                          | (guard,wl1) ->
                              let uu____24968 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24968))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24971,uu____24972) ->
                  let head1 =
                    let uu____24990 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24990
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25036 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25036
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25082 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25082
                    then
                      let uu____25086 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25088 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25090 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25086 uu____25088 uu____25090
                    else ());
                   (let no_free_uvars t =
                      (let uu____25104 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25104) &&
                        (let uu____25108 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25108)
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
                      let uu____25127 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25127 = FStar_Syntax_Util.Equal  in
                    let uu____25128 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25128
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25132 = equal t1 t2  in
                         (if uu____25132
                          then
                            let uu____25135 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25135
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25140 =
                            let uu____25147 = equal t1 t2  in
                            if uu____25147
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25160 = mk_eq2 wl env orig t1 t2  in
                               match uu____25160 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25140 with
                          | (guard,wl1) ->
                              let uu____25181 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25181))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25184,FStar_Syntax_Syntax.Tm_match uu____25185) ->
                  let head1 =
                    let uu____25209 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25209
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25255 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25255
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25301 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25301
                    then
                      let uu____25305 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25307 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25309 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25305 uu____25307 uu____25309
                    else ());
                   (let no_free_uvars t =
                      (let uu____25323 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25323) &&
                        (let uu____25327 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25327)
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
                      let uu____25346 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25346 = FStar_Syntax_Util.Equal  in
                    let uu____25347 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25347
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25351 = equal t1 t2  in
                         (if uu____25351
                          then
                            let uu____25354 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25354
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25359 =
                            let uu____25366 = equal t1 t2  in
                            if uu____25366
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25379 = mk_eq2 wl env orig t1 t2  in
                               match uu____25379 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25359 with
                          | (guard,wl1) ->
                              let uu____25400 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25400))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25403,FStar_Syntax_Syntax.Tm_uinst uu____25404) ->
                  let head1 =
                    let uu____25412 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25412
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25458 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25458
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25504 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25504
                    then
                      let uu____25508 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25510 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25512 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25508 uu____25510 uu____25512
                    else ());
                   (let no_free_uvars t =
                      (let uu____25526 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25526) &&
                        (let uu____25530 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25530)
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
                      let uu____25549 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25549 = FStar_Syntax_Util.Equal  in
                    let uu____25550 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25550
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25554 = equal t1 t2  in
                         (if uu____25554
                          then
                            let uu____25557 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25557
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25562 =
                            let uu____25569 = equal t1 t2  in
                            if uu____25569
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25582 = mk_eq2 wl env orig t1 t2  in
                               match uu____25582 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25562 with
                          | (guard,wl1) ->
                              let uu____25603 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25603))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25606,FStar_Syntax_Syntax.Tm_name uu____25607) ->
                  let head1 =
                    let uu____25609 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25609
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25655 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25655
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25695 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25695
                    then
                      let uu____25699 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25701 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25703 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25699 uu____25701 uu____25703
                    else ());
                   (let no_free_uvars t =
                      (let uu____25717 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25717) &&
                        (let uu____25721 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25721)
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
                      let uu____25740 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25740 = FStar_Syntax_Util.Equal  in
                    let uu____25741 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25741
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25745 = equal t1 t2  in
                         (if uu____25745
                          then
                            let uu____25748 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25748
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25753 =
                            let uu____25760 = equal t1 t2  in
                            if uu____25760
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25773 = mk_eq2 wl env orig t1 t2  in
                               match uu____25773 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25753 with
                          | (guard,wl1) ->
                              let uu____25794 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25794))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25797,FStar_Syntax_Syntax.Tm_constant uu____25798) ->
                  let head1 =
                    let uu____25800 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25800
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25840 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25840
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25880 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25880
                    then
                      let uu____25884 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25886 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25888 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25884 uu____25886 uu____25888
                    else ());
                   (let no_free_uvars t =
                      (let uu____25902 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25902) &&
                        (let uu____25906 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25906)
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
                      let uu____25925 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25925 = FStar_Syntax_Util.Equal  in
                    let uu____25926 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25926
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25930 = equal t1 t2  in
                         (if uu____25930
                          then
                            let uu____25933 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25933
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25938 =
                            let uu____25945 = equal t1 t2  in
                            if uu____25945
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25958 = mk_eq2 wl env orig t1 t2  in
                               match uu____25958 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25938 with
                          | (guard,wl1) ->
                              let uu____25979 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25979))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25982,FStar_Syntax_Syntax.Tm_fvar uu____25983) ->
                  let head1 =
                    let uu____25985 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25985
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26031 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26031
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26077 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26077
                    then
                      let uu____26081 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26083 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26085 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26081 uu____26083 uu____26085
                    else ());
                   (let no_free_uvars t =
                      (let uu____26099 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26099) &&
                        (let uu____26103 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26103)
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
                      let uu____26122 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26122 = FStar_Syntax_Util.Equal  in
                    let uu____26123 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26123
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26127 = equal t1 t2  in
                         (if uu____26127
                          then
                            let uu____26130 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26130
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26135 =
                            let uu____26142 = equal t1 t2  in
                            if uu____26142
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26155 = mk_eq2 wl env orig t1 t2  in
                               match uu____26155 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26135 with
                          | (guard,wl1) ->
                              let uu____26176 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26176))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26179,FStar_Syntax_Syntax.Tm_app uu____26180) ->
                  let head1 =
                    let uu____26198 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26198
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26238 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26238
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26278 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26278
                    then
                      let uu____26282 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26284 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26286 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26282 uu____26284 uu____26286
                    else ());
                   (let no_free_uvars t =
                      (let uu____26300 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26300) &&
                        (let uu____26304 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26304)
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
                      let uu____26323 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26323 = FStar_Syntax_Util.Equal  in
                    let uu____26324 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26324
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26328 = equal t1 t2  in
                         (if uu____26328
                          then
                            let uu____26331 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26331
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26336 =
                            let uu____26343 = equal t1 t2  in
                            if uu____26343
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26356 = mk_eq2 wl env orig t1 t2  in
                               match uu____26356 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26336 with
                          | (guard,wl1) ->
                              let uu____26377 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26377))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26380,FStar_Syntax_Syntax.Tm_let uu____26381) ->
                  let uu____26408 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26408
                  then
                    let uu____26411 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26411
                  else
                    (let uu____26414 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26414 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26417,uu____26418) ->
                  let uu____26432 =
                    let uu____26438 =
                      let uu____26440 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26442 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26444 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26446 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26440 uu____26442 uu____26444 uu____26446
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26438)
                     in
                  FStar_Errors.raise_error uu____26432
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26450,FStar_Syntax_Syntax.Tm_let uu____26451) ->
                  let uu____26465 =
                    let uu____26471 =
                      let uu____26473 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26475 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26477 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26479 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26473 uu____26475 uu____26477 uu____26479
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26471)
                     in
                  FStar_Errors.raise_error uu____26465
                    t1.FStar_Syntax_Syntax.pos
              | uu____26483 ->
                  let uu____26488 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26488 orig))))

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
          (let uu____26554 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26554
           then
             let uu____26559 =
               let uu____26561 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26561  in
             let uu____26562 =
               let uu____26564 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26564  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26559 uu____26562
           else ());
          (let uu____26568 =
             let uu____26570 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26570  in
           if uu____26568
           then
             let uu____26573 =
               FStar_Thunk.mk
                 (fun uu____26578  ->
                    let uu____26579 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26581 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26579 uu____26581)
                in
             giveup env uu____26573 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26603 =
                  FStar_Thunk.mk
                    (fun uu____26608  ->
                       let uu____26609 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26611 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26609 uu____26611)
                   in
                giveup env uu____26603 orig)
             else
               (let uu____26616 =
                  FStar_List.fold_left2
                    (fun uu____26637  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26637 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26658 =
                                 let uu____26663 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26664 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26663
                                   FStar_TypeChecker_Common.EQ uu____26664
                                   "effect universes"
                                  in
                               (match uu____26658 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26616 with
                | (univ_sub_probs,wl1) ->
                    let uu____26684 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26684 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26692 =
                           FStar_List.fold_right2
                             (fun uu____26729  ->
                                fun uu____26730  ->
                                  fun uu____26731  ->
                                    match (uu____26729, uu____26730,
                                            uu____26731)
                                    with
                                    | ((a1,uu____26775),(a2,uu____26777),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26810 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26810 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26692 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26837 =
                                  let uu____26840 =
                                    let uu____26843 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26843
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26840
                                   in
                                FStar_List.append univ_sub_probs uu____26837
                                 in
                              let guard =
                                let guard =
                                  let uu____26865 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26865  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3500_26874 = wl3  in
                                {
                                  attempting = (uu___3500_26874.attempting);
                                  wl_deferred = (uu___3500_26874.wl_deferred);
                                  ctr = (uu___3500_26874.ctr);
                                  defer_ok = (uu___3500_26874.defer_ok);
                                  smt_ok = (uu___3500_26874.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3500_26874.umax_heuristic_ok);
                                  tcenv = (uu___3500_26874.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26876 = attempt sub_probs wl5  in
                              solve env uu____26876))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26894 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26894
           then
             let uu____26899 =
               let uu____26901 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26901
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26903 =
               let uu____26905 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26905
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26899 uu____26903
           else ());
          (let uu____26910 =
             let uu____26915 =
               let uu____26920 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26920
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26915
               (fun uu____26937  ->
                  match uu____26937 with
                  | (c,g) ->
                      let uu____26948 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26948, g))
              in
           match uu____26910 with
           | (c12,g_lift) ->
               ((let uu____26952 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26952
                 then
                   let uu____26957 =
                     let uu____26959 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26959
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26961 =
                     let uu____26963 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26963
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26957 uu____26961
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3520_26973 = wl  in
                     {
                       attempting = (uu___3520_26973.attempting);
                       wl_deferred = (uu___3520_26973.wl_deferred);
                       ctr = (uu___3520_26973.ctr);
                       defer_ok = (uu___3520_26973.defer_ok);
                       smt_ok = (uu___3520_26973.smt_ok);
                       umax_heuristic_ok =
                         (uu___3520_26973.umax_heuristic_ok);
                       tcenv = (uu___3520_26973.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26974 =
                     let rec is_uvar1 t =
                       let uu____26988 =
                         let uu____26989 = FStar_Syntax_Subst.compress t  in
                         uu____26989.FStar_Syntax_Syntax.n  in
                       match uu____26988 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26993 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27008) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27014) ->
                           is_uvar1 t1
                       | uu____27039 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27073  ->
                          fun uu____27074  ->
                            fun uu____27075  ->
                              match (uu____27073, uu____27074, uu____27075)
                              with
                              | ((a1,uu____27119),(a2,uu____27121),(is_sub_probs,wl2))
                                  ->
                                  let uu____27154 = is_uvar1 a1  in
                                  if uu____27154
                                  then
                                    ((let uu____27164 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27164
                                      then
                                        let uu____27169 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27171 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27169 uu____27171
                                      else ());
                                     (let uu____27176 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27176 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26974 with
                   | (is_sub_probs,wl2) ->
                       let uu____27204 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27204 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27212 =
                              let uu____27217 =
                                let uu____27218 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27218
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27217
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27212 with
                             | (uu____27225,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27236 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27238 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27236 s uu____27238
                                    in
                                 let uu____27241 =
                                   let uu____27270 =
                                     let uu____27271 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27271.FStar_Syntax_Syntax.n  in
                                   match uu____27270 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27331 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27331 with
                                        | (a::bs1,c3) ->
                                            let uu____27387 =
                                              let uu____27406 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27406
                                                (fun uu____27510  ->
                                                   match uu____27510 with
                                                   | (l1,l2) ->
                                                       let uu____27583 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27583))
                                               in
                                            (match uu____27387 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27688 ->
                                       let uu____27689 =
                                         let uu____27695 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27695)
                                          in
                                       FStar_Errors.raise_error uu____27689 r
                                    in
                                 (match uu____27241 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27771 =
                                        let uu____27778 =
                                          let uu____27779 =
                                            let uu____27780 =
                                              let uu____27787 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27787,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27780
                                             in
                                          [uu____27779]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27778
                                          (fun b  ->
                                             let uu____27803 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27805 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27807 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27803 uu____27805
                                               uu____27807) r
                                         in
                                      (match uu____27771 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27817 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27817
                                             then
                                               let uu____27822 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27831 =
                                                          let uu____27833 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27833
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27831) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27822
                                             else ());
                                            (let wl4 =
                                               let uu___3592_27841 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3592_27841.attempting);
                                                 wl_deferred =
                                                   (uu___3592_27841.wl_deferred);
                                                 ctr = (uu___3592_27841.ctr);
                                                 defer_ok =
                                                   (uu___3592_27841.defer_ok);
                                                 smt_ok =
                                                   (uu___3592_27841.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3592_27841.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3592_27841.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27866 =
                                                        let uu____27873 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27873, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27866) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27890 =
                                               let f_sort_is =
                                                 let uu____27900 =
                                                   let uu____27901 =
                                                     let uu____27904 =
                                                       let uu____27905 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27905.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27904
                                                      in
                                                   uu____27901.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27900 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27916,uu____27917::is)
                                                     ->
                                                     let uu____27959 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27959
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27992 ->
                                                     let uu____27993 =
                                                       let uu____27999 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27999)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27993 r
                                                  in
                                               let uu____28005 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28040  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28040
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28061 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28061
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28005
                                                in
                                             match uu____27890 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28086 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28086
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28087 =
                                                   let g_sort_is =
                                                     let uu____28097 =
                                                       let uu____28098 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28098.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28097 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28103,uu____28104::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28164 ->
                                                         let uu____28165 =
                                                           let uu____28171 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28171)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28165 r
                                                      in
                                                   let uu____28177 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28212  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28212
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28233
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28233
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28177
                                                    in
                                                 (match uu____28087 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28260 =
                                                          let uu____28265 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28266 =
                                                            let uu____28267 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28267
                                                             in
                                                          (uu____28265,
                                                            uu____28266)
                                                           in
                                                        match uu____28260
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28295 =
                                                          let uu____28298 =
                                                            let uu____28301 =
                                                              let uu____28304
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28304
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28301
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28298
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28295
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28328 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28328
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
                                                        let uu____28339 =
                                                          let uu____28342 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28345  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28345)
                                                            uu____28342
                                                           in
                                                        solve_prob orig
                                                          uu____28339 [] wl6
                                                         in
                                                      let uu____28346 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28346))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28369 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28371 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28371]
              | x -> x  in
            let c12 =
              let uu___3658_28374 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3658_28374.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3658_28374.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3658_28374.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3658_28374.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28375 =
              let uu____28380 =
                FStar_All.pipe_right
                  (let uu___3661_28382 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3661_28382.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3661_28382.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3661_28382.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3661_28382.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28380
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28375
              (fun uu____28396  ->
                 match uu____28396 with
                 | (c,g) ->
                     let uu____28403 =
                       let uu____28405 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28405  in
                     if uu____28403
                     then
                       let uu____28408 =
                         let uu____28414 =
                           let uu____28416 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28418 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28416 uu____28418
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28414)
                          in
                       FStar_Errors.raise_error uu____28408 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28424 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28424
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28430 = lift_c1 ()  in
               solve_eq uu____28430 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28439  ->
                         match uu___31_28439 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28444 -> false))
                  in
               let uu____28446 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28476)::uu____28477,(wp2,uu____28479)::uu____28480)
                     -> (wp1, wp2)
                 | uu____28553 ->
                     let uu____28578 =
                       let uu____28584 =
                         let uu____28586 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28588 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28586 uu____28588
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28584)
                        in
                     FStar_Errors.raise_error uu____28578
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28446 with
               | (wpc1,wpc2) ->
                   let uu____28598 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28598
                   then
                     let uu____28601 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28601 wl
                   else
                     (let uu____28605 =
                        let uu____28612 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28612  in
                      match uu____28605 with
                      | (c2_decl,qualifiers) ->
                          let uu____28633 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28633
                          then
                            let c1_repr =
                              let uu____28640 =
                                let uu____28641 =
                                  let uu____28642 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28642  in
                                let uu____28643 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28641 uu____28643
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28640
                               in
                            let c2_repr =
                              let uu____28646 =
                                let uu____28647 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28648 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28647 uu____28648
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28646
                               in
                            let uu____28650 =
                              let uu____28655 =
                                let uu____28657 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28659 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28657
                                  uu____28659
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28655
                               in
                            (match uu____28650 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28665 = attempt [prob] wl2  in
                                 solve env uu____28665)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28685 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28685
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28708 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28708
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
                                        let uu____28718 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28718 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28725 =
                                        let uu____28732 =
                                          let uu____28733 =
                                            let uu____28750 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28753 =
                                              let uu____28764 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28764; wpc1_2]  in
                                            (uu____28750, uu____28753)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28733
                                           in
                                        FStar_Syntax_Syntax.mk uu____28732
                                         in
                                      uu____28725
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
                                     let uu____28813 =
                                       let uu____28820 =
                                         let uu____28821 =
                                           let uu____28838 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28841 =
                                             let uu____28852 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28861 =
                                               let uu____28872 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28872; wpc1_2]  in
                                             uu____28852 :: uu____28861  in
                                           (uu____28838, uu____28841)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28821
                                          in
                                       FStar_Syntax_Syntax.mk uu____28820  in
                                     uu____28813 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28926 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28926
                              then
                                let uu____28931 =
                                  let uu____28933 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28933
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28931
                              else ());
                             (let uu____28937 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28937 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28946 =
                                      let uu____28949 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28952  ->
                                           FStar_Pervasives_Native.Some
                                             _28952) uu____28949
                                       in
                                    solve_prob orig uu____28946 [] wl1  in
                                  let uu____28953 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28953))))
           in
        let uu____28954 = FStar_Util.physical_equality c1 c2  in
        if uu____28954
        then
          let uu____28957 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28957
        else
          ((let uu____28961 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28961
            then
              let uu____28966 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28968 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28966
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28968
            else ());
           (let uu____28973 =
              let uu____28982 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28985 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28982, uu____28985)  in
            match uu____28973 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29003),FStar_Syntax_Syntax.Total
                    (t2,uu____29005)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29022 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29022 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29024,FStar_Syntax_Syntax.Total uu____29025) ->
                     let uu____29042 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29042 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29046),FStar_Syntax_Syntax.Total
                    (t2,uu____29048)) ->
                     let uu____29065 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29065 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29068),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29070)) ->
                     let uu____29087 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29087 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29090),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29092)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29109 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29109 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29112),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29114)) ->
                     let uu____29131 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29131 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29134,FStar_Syntax_Syntax.Comp uu____29135) ->
                     let uu____29144 =
                       let uu___3785_29147 = problem  in
                       let uu____29150 =
                         let uu____29151 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29151
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3785_29147.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29150;
                         FStar_TypeChecker_Common.relation =
                           (uu___3785_29147.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3785_29147.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3785_29147.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3785_29147.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3785_29147.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3785_29147.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3785_29147.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3785_29147.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29144 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29152,FStar_Syntax_Syntax.Comp uu____29153) ->
                     let uu____29162 =
                       let uu___3785_29165 = problem  in
                       let uu____29168 =
                         let uu____29169 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29169
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3785_29165.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29168;
                         FStar_TypeChecker_Common.relation =
                           (uu___3785_29165.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3785_29165.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3785_29165.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3785_29165.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3785_29165.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3785_29165.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3785_29165.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3785_29165.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29162 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29170,FStar_Syntax_Syntax.GTotal uu____29171) ->
                     let uu____29180 =
                       let uu___3797_29183 = problem  in
                       let uu____29186 =
                         let uu____29187 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29187
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29183.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3797_29183.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29183.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29186;
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29183.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29183.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29183.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29183.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29183.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29183.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29180 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29188,FStar_Syntax_Syntax.Total uu____29189) ->
                     let uu____29198 =
                       let uu___3797_29201 = problem  in
                       let uu____29204 =
                         let uu____29205 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29205
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29201.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3797_29201.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29201.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29204;
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29201.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29201.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29201.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29201.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29201.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29201.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29198 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29206,FStar_Syntax_Syntax.Comp uu____29207) ->
                     let uu____29208 =
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
                     if uu____29208
                     then
                       let uu____29211 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29211 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29218 =
                            let uu____29223 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29223
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29232 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29233 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29232, uu____29233))
                             in
                          match uu____29218 with
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
                           (let uu____29241 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29241
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29249 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29249 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29252 =
                                  FStar_Thunk.mk
                                    (fun uu____29257  ->
                                       let uu____29258 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29260 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29258 uu____29260)
                                   in
                                giveup env uu____29252 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29271 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29271 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29321 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29321 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29346 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29377  ->
                match uu____29377 with
                | (u1,u2) ->
                    let uu____29385 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29387 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29385 uu____29387))
         in
      FStar_All.pipe_right uu____29346 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29424,[])) when
          let uu____29451 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29451 -> "{}"
      | uu____29454 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29481 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29481
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29493 =
              FStar_List.map
                (fun uu____29506  ->
                   match uu____29506 with
                   | (uu____29513,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29493 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29524 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29524 imps
  
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
                  let uu____29581 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29581
                  then
                    let uu____29589 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29591 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29589
                      (rel_to_string rel) uu____29591
                  else "TOP"  in
                let uu____29597 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29597 with
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
              let uu____29657 =
                let uu____29660 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29663  -> FStar_Pervasives_Native.Some _29663)
                  uu____29660
                 in
              FStar_Syntax_Syntax.new_bv uu____29657 t1  in
            let uu____29664 =
              let uu____29669 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29669
               in
            match uu____29664 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29727 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29727
         then
           let uu____29732 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29732
         else ());
        (let uu____29739 =
           FStar_Util.record_time (fun uu____29746  -> solve env probs)  in
         match uu____29739 with
         | (sol,ms) ->
             ((let uu____29758 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29758
               then
                 let uu____29763 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29763
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29776 =
                     FStar_Util.record_time
                       (fun uu____29783  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29776 with
                    | ((),ms1) ->
                        ((let uu____29794 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29794
                          then
                            let uu____29799 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29799
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29811 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29811
                     then
                       let uu____29818 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29818
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
          ((let uu____29844 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29844
            then
              let uu____29849 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29849
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29857 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29857
             then
               let uu____29862 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29862
             else ());
            (let f2 =
               let uu____29868 =
                 let uu____29869 = FStar_Syntax_Util.unmeta f1  in
                 uu____29869.FStar_Syntax_Syntax.n  in
               match uu____29868 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29873 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3914_29874 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3914_29874.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3914_29874.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3914_29874.FStar_TypeChecker_Common.implicits)
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
            let uu____29917 =
              let uu____29918 =
                let uu____29919 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29920  ->
                       FStar_TypeChecker_Common.NonTrivial _29920)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29919;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29918  in
            FStar_All.pipe_left
              (fun _29927  -> FStar_Pervasives_Native.Some _29927)
              uu____29917
  
let with_guard_no_simp :
  'Auu____29937 .
    'Auu____29937 ->
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
            let uu____29977 =
              let uu____29978 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29979  -> FStar_TypeChecker_Common.NonTrivial _29979)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29978;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29977
  
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
          (let uu____30012 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30012
           then
             let uu____30017 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30019 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30017
               uu____30019
           else ());
          (let uu____30024 =
             let uu____30029 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30029
              in
           match uu____30024 with
           | (prob,wl) ->
               let g =
                 let uu____30037 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30045  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30037  in
               ((let uu____30063 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30063
                 then
                   let uu____30068 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30068
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
        let uu____30089 = try_teq true env t1 t2  in
        match uu____30089 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30094 = FStar_TypeChecker_Env.get_range env  in
              let uu____30095 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30094 uu____30095);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30103 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30103
              then
                let uu____30108 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30110 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30112 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30108
                  uu____30110 uu____30112
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
        (let uu____30136 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30136
         then
           let uu____30141 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30143 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30141
             uu____30143
         else ());
        (let uu____30148 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30148 with
         | (prob,x,wl) ->
             let g =
               let uu____30163 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30172  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30163  in
             ((let uu____30190 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30190
               then
                 let uu____30195 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30195
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30203 =
                     let uu____30204 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30204 g1  in
                   FStar_Pervasives_Native.Some uu____30203)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30226 = FStar_TypeChecker_Env.get_range env  in
          let uu____30227 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30226 uu____30227
  
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
        (let uu____30256 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30256
         then
           let uu____30261 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30263 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30261 uu____30263
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30274 =
           let uu____30281 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30281 "sub_comp"
            in
         match uu____30274 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30294 =
                 FStar_Util.record_time
                   (fun uu____30306  ->
                      let uu____30307 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30316  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30307)
                  in
               match uu____30294 with
               | (r,ms) ->
                   ((let uu____30344 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30344
                     then
                       let uu____30349 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30351 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30353 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30349 uu____30351
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30353
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
      fun uu____30391  ->
        match uu____30391 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30434 =
                 let uu____30440 =
                   let uu____30442 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30444 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30442 uu____30444
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30440)  in
               let uu____30448 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30434 uu____30448)
               in
            let equiv1 v1 v' =
              let uu____30461 =
                let uu____30466 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30467 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30466, uu____30467)  in
              match uu____30461 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30487 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30518 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30518 with
                      | FStar_Syntax_Syntax.U_unif uu____30525 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30554  ->
                                    match uu____30554 with
                                    | (u,v') ->
                                        let uu____30563 = equiv1 v1 v'  in
                                        if uu____30563
                                        then
                                          let uu____30568 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30568 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30589 -> []))
               in
            let uu____30594 =
              let wl =
                let uu___4025_30598 = empty_worklist env  in
                {
                  attempting = (uu___4025_30598.attempting);
                  wl_deferred = (uu___4025_30598.wl_deferred);
                  ctr = (uu___4025_30598.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4025_30598.smt_ok);
                  umax_heuristic_ok = (uu___4025_30598.umax_heuristic_ok);
                  tcenv = (uu___4025_30598.tcenv);
                  wl_implicits = (uu___4025_30598.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30617  ->
                      match uu____30617 with
                      | (lb,v1) ->
                          let uu____30624 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30624 with
                           | USolved wl1 -> ()
                           | uu____30627 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30638 =
              match uu____30638 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30650) -> true
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
                      uu____30674,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30676,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30687) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30695,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30704 -> false)
               in
            let uu____30710 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30727  ->
                      match uu____30727 with
                      | (u,v1) ->
                          let uu____30735 = check_ineq (u, v1)  in
                          if uu____30735
                          then true
                          else
                            ((let uu____30743 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30743
                              then
                                let uu____30748 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30750 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30748
                                  uu____30750
                              else ());
                             false)))
               in
            if uu____30710
            then ()
            else
              ((let uu____30760 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30760
                then
                  ((let uu____30766 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30766);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30778 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30778))
                else ());
               (let uu____30791 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30791))
  
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
        let fail1 uu____30864 =
          match uu____30864 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4102_30887 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4102_30887.attempting);
            wl_deferred = (uu___4102_30887.wl_deferred);
            ctr = (uu___4102_30887.ctr);
            defer_ok;
            smt_ok = (uu___4102_30887.smt_ok);
            umax_heuristic_ok = (uu___4102_30887.umax_heuristic_ok);
            tcenv = (uu___4102_30887.tcenv);
            wl_implicits = (uu___4102_30887.wl_implicits)
          }  in
        (let uu____30890 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30890
         then
           let uu____30895 = FStar_Util.string_of_bool defer_ok  in
           let uu____30897 = wl_to_string wl  in
           let uu____30899 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30895 uu____30897 uu____30899
         else ());
        (let g1 =
           let uu____30905 = solve_and_commit env wl fail1  in
           match uu____30905 with
           | FStar_Pervasives_Native.Some
               (uu____30912::uu____30913,uu____30914) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4117_30943 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4117_30943.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4117_30943.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30944 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4122_30953 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4122_30953.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4122_30953.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4122_30953.FStar_TypeChecker_Common.implicits)
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
            let uu___4134_31030 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4134_31030.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4134_31030.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4134_31030.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31031 =
            let uu____31033 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31033  in
          if uu____31031
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31045 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31046 =
                       let uu____31048 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31048
                        in
                     FStar_Errors.diag uu____31045 uu____31046)
                  else ();
                  (let vc1 =
                     let uu____31054 =
                       let uu____31058 =
                         let uu____31060 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31060  in
                       FStar_Pervasives_Native.Some uu____31058  in
                     FStar_Profiling.profile
                       (fun uu____31063  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31054 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31067 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31068 =
                        let uu____31070 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31070
                         in
                      FStar_Errors.diag uu____31067 uu____31068)
                   else ();
                   (let uu____31076 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31076
                      "discharge_guard'" env vc1);
                   (let uu____31078 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31078 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31087 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31088 =
                                let uu____31090 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31090
                                 in
                              FStar_Errors.diag uu____31087 uu____31088)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31100 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31101 =
                                let uu____31103 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31103
                                 in
                              FStar_Errors.diag uu____31100 uu____31101)
                           else ();
                           (let vcs =
                              let uu____31117 = FStar_Options.use_tactics ()
                                 in
                              if uu____31117
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31139  ->
                                     (let uu____31141 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31141);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31185  ->
                                              match uu____31185 with
                                              | (env1,goal,opts) ->
                                                  let uu____31201 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31201, opts)))))
                              else
                                (let uu____31205 =
                                   let uu____31212 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31212)  in
                                 [uu____31205])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31245  ->
                                    match uu____31245 with
                                    | (env1,goal,opts) ->
                                        let uu____31255 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31255 with
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
                                                (let uu____31266 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31267 =
                                                   let uu____31269 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31271 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31269 uu____31271
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31266 uu____31267)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31278 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31279 =
                                                   let uu____31281 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31281
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31278 uu____31279)
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
      let uu____31299 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31299 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31308 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31308
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31322 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31322 with
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
        let uu____31352 = try_teq false env t1 t2  in
        match uu____31352 with
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
            let uu____31396 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31396 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31409 ->
                     let uu____31422 =
                       let uu____31423 = FStar_Syntax_Subst.compress r  in
                       uu____31423.FStar_Syntax_Syntax.n  in
                     (match uu____31422 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31428) ->
                          unresolved ctx_u'
                      | uu____31445 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31469 = acc  in
            match uu____31469 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31488 = hd1  in
                     (match uu____31488 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31499 = unresolved ctx_u  in
                             if uu____31499
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31523 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31523
                                     then
                                       let uu____31527 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31527
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31536 = teq_nosmt env1 t tm
                                          in
                                       match uu____31536 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4247_31546 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4247_31546.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4250_31554 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4250_31554.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4250_31554.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4250_31554.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4254_31565 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4254_31565.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4254_31565.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4254_31565.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4254_31565.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4254_31565.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4254_31565.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4254_31565.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4254_31565.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4254_31565.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4254_31565.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4254_31565.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4254_31565.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4254_31565.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4254_31565.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4254_31565.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4254_31565.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4254_31565.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4254_31565.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4254_31565.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4254_31565.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4254_31565.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4254_31565.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4254_31565.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4254_31565.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4254_31565.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4254_31565.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4254_31565.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4254_31565.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4254_31565.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4254_31565.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4254_31565.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4254_31565.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4254_31565.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4254_31565.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4254_31565.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4254_31565.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4254_31565.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4254_31565.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4254_31565.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4254_31565.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4254_31565.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4254_31565.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4254_31565.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4254_31565.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4254_31565.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4254_31565.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4259_31570 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4259_31570.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4259_31570.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4259_31570.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4259_31570.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4259_31570.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4259_31570.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4259_31570.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4259_31570.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4259_31570.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4259_31570.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4259_31570.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4259_31570.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4259_31570.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4259_31570.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4259_31570.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4259_31570.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4259_31570.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4259_31570.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4259_31570.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4259_31570.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4259_31570.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4259_31570.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4259_31570.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4259_31570.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4259_31570.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4259_31570.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4259_31570.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4259_31570.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4259_31570.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4259_31570.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4259_31570.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4259_31570.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4259_31570.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4259_31570.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4259_31570.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4259_31570.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4259_31570.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31575 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31575
                                   then
                                     let uu____31580 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31582 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31584 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31586 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31580 uu____31582 uu____31584
                                       reason uu____31586
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4265_31593  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31600 =
                                             let uu____31610 =
                                               let uu____31618 =
                                                 let uu____31620 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31622 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31624 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31620 uu____31622
                                                   uu____31624
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31618, r)
                                                in
                                             [uu____31610]  in
                                           FStar_Errors.add_errors
                                             uu____31600);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31643 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31654  ->
                                               let uu____31655 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31657 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31659 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31655 uu____31657
                                                 reason uu____31659)) env2 g1
                                         true
                                        in
                                     match uu____31643 with
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
          let uu___4277_31667 = g  in
          let uu____31668 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4277_31667.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4277_31667.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4277_31667.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31668
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
        let uu____31708 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31708 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31709 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31709
      | imp::uu____31711 ->
          let uu____31714 =
            let uu____31720 =
              let uu____31722 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31724 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31722 uu____31724
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31720)
             in
          FStar_Errors.raise_error uu____31714
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31744 = teq env t1 t2  in
        force_trivial_guard env uu____31744
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31763 = teq_nosmt env t1 t2  in
        match uu____31763 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4302_31782 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4302_31782.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4302_31782.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4302_31782.FStar_TypeChecker_Common.implicits)
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
        (let uu____31818 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31818
         then
           let uu____31823 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31825 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31823
             uu____31825
         else ());
        (let uu____31830 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31830 with
         | (prob,x,wl) ->
             let g =
               let uu____31849 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31858  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31849  in
             ((let uu____31876 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31876
               then
                 let uu____31881 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31883 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31885 =
                   let uu____31887 = FStar_Util.must g  in
                   guard_to_string env uu____31887  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31881 uu____31883 uu____31885
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
        let uu____31924 = check_subtyping env t1 t2  in
        match uu____31924 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31943 =
              let uu____31944 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31944 g  in
            FStar_Pervasives_Native.Some uu____31943
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31963 = check_subtyping env t1 t2  in
        match uu____31963 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31982 =
              let uu____31983 =
                let uu____31984 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31984]  in
              FStar_TypeChecker_Env.close_guard env uu____31983 g  in
            FStar_Pervasives_Native.Some uu____31982
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32022 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32022
         then
           let uu____32027 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32029 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32027
             uu____32029
         else ());
        (let uu____32034 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32034 with
         | (prob,x,wl) ->
             let g =
               let uu____32049 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32058  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32049  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32079 =
                      let uu____32080 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32080]  in
                    FStar_TypeChecker_Env.close_guard env uu____32079 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32121 = subtype_nosmt env t1 t2  in
        match uu____32121 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  