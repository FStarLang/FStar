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
                 let uu____2747 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2749 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2747, uu____2749)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2756 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2758 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2756, uu____2758)
              in
           match uu____2731 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2786  ->
            match uu___15_2786 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2798 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2802 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2802 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2833  ->
           match uu___16_2833 with
           | UNIV uu____2836 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2843 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2843
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
        (fun uu___17_2871  ->
           match uu___17_2871 with
           | UNIV (u',t) ->
               let uu____2876 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2876
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2883 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2895 =
        let uu____2896 =
          let uu____2897 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2897
           in
        FStar_Syntax_Subst.compress uu____2896  in
      FStar_All.pipe_right uu____2895 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2909 =
        let uu____2910 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2910  in
      FStar_All.pipe_right uu____2909 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2922 =
        let uu____2926 =
          let uu____2928 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____2928  in
        FStar_Pervasives_Native.Some uu____2926  in
      FStar_Profiling.profile (fun uu____2931  -> sn' env t) uu____2922
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
          let uu____2956 =
            let uu____2960 =
              let uu____2962 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____2962  in
            FStar_Pervasives_Native.Some uu____2960  in
          FStar_Profiling.profile
            (fun uu____2965  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2956
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2973 = FStar_Syntax_Util.head_and_args t  in
    match uu____2973 with
    | (h,uu____2992) ->
        let uu____3017 =
          let uu____3018 = FStar_Syntax_Subst.compress h  in
          uu____3018.FStar_Syntax_Syntax.n  in
        (match uu____3017 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3023 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3036 =
        let uu____3040 =
          let uu____3042 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3042  in
        FStar_Pervasives_Native.Some uu____3040  in
      FStar_Profiling.profile
        (fun uu____3047  ->
           let uu____3048 = should_strongly_reduce t  in
           if uu____3048
           then
             let uu____3051 =
               let uu____3052 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3052  in
             FStar_All.pipe_right uu____3051 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3036 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3063 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3063) ->
        (FStar_Syntax_Syntax.term * 'Auu____3063)
  =
  fun env  ->
    fun t  ->
      let uu____3086 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3086, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3138  ->
              match uu____3138 with
              | (x,imp) ->
                  let uu____3157 =
                    let uu___456_3158 = x  in
                    let uu____3159 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___456_3158.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___456_3158.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3159
                    }  in
                  (uu____3157, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3183 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3183
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3187 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3187
        | uu____3190 -> u2  in
      let uu____3191 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3191
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3208 =
          let uu____3212 =
            let uu____3214 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3214  in
          FStar_Pervasives_Native.Some uu____3212  in
        FStar_Profiling.profile
          (fun uu____3217  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3208 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3339 = norm_refinement env t12  in
                 match uu____3339 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3354;
                     FStar_Syntax_Syntax.vars = uu____3355;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3379 =
                       let uu____3381 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3383 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3381 uu____3383
                        in
                     failwith uu____3379)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3399 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3399
          | FStar_Syntax_Syntax.Tm_uinst uu____3400 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3437 =
                   let uu____3438 = FStar_Syntax_Subst.compress t1'  in
                   uu____3438.FStar_Syntax_Syntax.n  in
                 match uu____3437 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3453 -> aux true t1'
                 | uu____3461 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3476 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3507 =
                   let uu____3508 = FStar_Syntax_Subst.compress t1'  in
                   uu____3508.FStar_Syntax_Syntax.n  in
                 match uu____3507 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3523 -> aux true t1'
                 | uu____3531 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3546 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3593 =
                   let uu____3594 = FStar_Syntax_Subst.compress t1'  in
                   uu____3594.FStar_Syntax_Syntax.n  in
                 match uu____3593 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3609 -> aux true t1'
                 | uu____3617 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3632 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3647 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3662 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3677 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3692 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3721 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3754 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3775 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3802 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3830 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3867 ->
              let uu____3874 =
                let uu____3876 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3878 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3876 uu____3878
                 in
              failwith uu____3874
          | FStar_Syntax_Syntax.Tm_ascribed uu____3893 ->
              let uu____3920 =
                let uu____3922 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3924 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3922 uu____3924
                 in
              failwith uu____3920
          | FStar_Syntax_Syntax.Tm_delayed uu____3939 ->
              let uu____3962 =
                let uu____3964 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3966 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3964 uu____3966
                 in
              failwith uu____3962
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3981 =
                let uu____3983 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3985 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3983 uu____3985
                 in
              failwith uu____3981
           in
        let uu____4000 = whnf env t1  in aux false uu____4000
  
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
      let uu____4045 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4045 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4086 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4086, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4113 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4113 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4173  ->
    match uu____4173 with
    | (t_base,refopt) ->
        let uu____4204 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4204 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4246 =
      let uu____4250 =
        let uu____4253 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4278  ->
                  match uu____4278 with | (uu____4286,uu____4287,x) -> x))
           in
        FStar_List.append wl.attempting uu____4253  in
      FStar_List.map (wl_prob_to_string wl) uu____4250  in
    FStar_All.pipe_right uu____4246 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4308 .
    ('Auu____4308 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4320  ->
    match uu____4320 with
    | (uu____4327,c,args) ->
        let uu____4330 = print_ctx_uvar c  in
        let uu____4332 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4330 uu____4332
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4342 = FStar_Syntax_Util.head_and_args t  in
    match uu____4342 with
    | (head1,_args) ->
        let uu____4386 =
          let uu____4387 = FStar_Syntax_Subst.compress head1  in
          uu____4387.FStar_Syntax_Syntax.n  in
        (match uu____4386 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4391 -> true
         | uu____4405 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4413 = FStar_Syntax_Util.head_and_args t  in
    match uu____4413 with
    | (head1,_args) ->
        let uu____4456 =
          let uu____4457 = FStar_Syntax_Subst.compress head1  in
          uu____4457.FStar_Syntax_Syntax.n  in
        (match uu____4456 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4461) -> u
         | uu____4478 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4503 = FStar_Syntax_Util.head_and_args t  in
      match uu____4503 with
      | (head1,args) ->
          let uu____4550 =
            let uu____4551 = FStar_Syntax_Subst.compress head1  in
            uu____4551.FStar_Syntax_Syntax.n  in
          (match uu____4550 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4559)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4592 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4617  ->
                         match uu___18_4617 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4622 =
                               let uu____4623 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4623.FStar_Syntax_Syntax.n  in
                             (match uu____4622 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4628 -> false)
                         | uu____4630 -> true))
                  in
               (match uu____4592 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4655 =
                        FStar_List.collect
                          (fun uu___19_4667  ->
                             match uu___19_4667 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4671 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4671]
                             | uu____4672 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4655 FStar_List.rev  in
                    let uu____4695 =
                      let uu____4702 =
                        let uu____4711 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4733  ->
                                  match uu___20_4733 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4737 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4737]
                                  | uu____4738 -> []))
                           in
                        FStar_All.pipe_right uu____4711 FStar_List.rev  in
                      let uu____4761 =
                        let uu____4764 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4764  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4702 uu____4761
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4695 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4800  ->
                                match uu____4800 with
                                | (x,i) ->
                                    let uu____4819 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4819, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4850  ->
                                match uu____4850 with
                                | (a,i) ->
                                    let uu____4869 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4869, i)) args_sol
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
           | uu____4891 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4913 =
          let uu____4936 =
            let uu____4937 = FStar_Syntax_Subst.compress k  in
            uu____4937.FStar_Syntax_Syntax.n  in
          match uu____4936 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5019 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5019)
              else
                (let uu____5054 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5054 with
                 | (ys',t1,uu____5087) ->
                     let uu____5092 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5092))
          | uu____5131 ->
              let uu____5132 =
                let uu____5137 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5137)  in
              ((ys, t), uu____5132)
           in
        match uu____4913 with
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
                 let uu____5232 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5232 c  in
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
               (let uu____5310 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5310
                then
                  let uu____5315 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5317 = print_ctx_uvar uv  in
                  let uu____5319 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5315 uu____5317 uu____5319
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5328 =
                   let uu____5330 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5330  in
                 let uu____5333 =
                   let uu____5336 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5336
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5328 uu____5333 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5369 =
               let uu____5370 =
                 let uu____5372 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5374 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5372 uu____5374
                  in
               failwith uu____5370  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5440  ->
                       match uu____5440 with
                       | (a,i) ->
                           let uu____5461 =
                             let uu____5462 = FStar_Syntax_Subst.compress a
                                in
                             uu____5462.FStar_Syntax_Syntax.n  in
                           (match uu____5461 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5488 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5498 =
                 let uu____5500 = is_flex g  in Prims.op_Negation uu____5500
                  in
               if uu____5498
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5509 = destruct_flex_t g wl  in
                  match uu____5509 with
                  | ((uu____5514,uv1,args),wl1) ->
                      ((let uu____5519 = args_as_binders args  in
                        assign_solution uu____5519 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___709_5521 = wl1  in
              {
                attempting = (uu___709_5521.attempting);
                wl_deferred = (uu___709_5521.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___709_5521.defer_ok);
                smt_ok = (uu___709_5521.smt_ok);
                umax_heuristic_ok = (uu___709_5521.umax_heuristic_ok);
                tcenv = (uu___709_5521.tcenv);
                wl_implicits = (uu___709_5521.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5546 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5546
         then
           let uu____5551 = FStar_Util.string_of_int pid  in
           let uu____5553 =
             let uu____5555 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5555 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5551 uu____5553
         else ());
        commit sol;
        (let uu___717_5569 = wl  in
         {
           attempting = (uu___717_5569.attempting);
           wl_deferred = (uu___717_5569.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___717_5569.defer_ok);
           smt_ok = (uu___717_5569.smt_ok);
           umax_heuristic_ok = (uu___717_5569.umax_heuristic_ok);
           tcenv = (uu___717_5569.tcenv);
           wl_implicits = (uu___717_5569.wl_implicits)
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
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____5635,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____5663 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____5663
              in
           (let uu____5669 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____5669
            then
              let uu____5674 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____5678 =
                let uu____5680 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____5680 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____5674 uu____5678
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____5715 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5715 FStar_Util.set_elements  in
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
      let uu____5755 = occurs uk t  in
      match uu____5755 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5794 =
                 let uu____5796 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5798 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5796 uu____5798
                  in
               FStar_Pervasives_Native.Some uu____5794)
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
            let uu____5918 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5918 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5969 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6026  ->
             match uu____6026 with
             | (x,uu____6038) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6056 = FStar_List.last bs  in
      match uu____6056 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6080) ->
          let uu____6091 =
            FStar_Util.prefix_until
              (fun uu___21_6106  ->
                 match uu___21_6106 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6109 -> false) g
             in
          (match uu____6091 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6123,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6160 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6160 with
        | (pfx,uu____6170) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6182 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6182 with
             | (uu____6190,src',wl1) ->
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
                 | uu____6304 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6305 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6369  ->
                  fun uu____6370  ->
                    match (uu____6369, uu____6370) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6473 =
                          let uu____6475 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6475
                           in
                        if uu____6473
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6509 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6509
                           then
                             let uu____6526 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6526)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6305 with | (isect,uu____6576) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6612 'Auu____6613 .
    (FStar_Syntax_Syntax.bv * 'Auu____6612) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6613) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6671  ->
              fun uu____6672  ->
                match (uu____6671, uu____6672) with
                | ((a,uu____6691),(b,uu____6693)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6709 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6709) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6740  ->
           match uu____6740 with
           | (y,uu____6747) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6757 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6757) Prims.list ->
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
                   let uu____6919 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6919
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6952 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7004 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7048 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7069 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7077  ->
    match uu___22_7077 with
    | MisMatch (d1,d2) ->
        let uu____7089 =
          let uu____7091 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7093 =
            let uu____7095 =
              let uu____7097 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7097 ")"  in
            Prims.op_Hat ") (" uu____7095  in
          Prims.op_Hat uu____7091 uu____7093  in
        Prims.op_Hat "MisMatch (" uu____7089
    | HeadMatch u ->
        let uu____7104 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7104
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7113  ->
    match uu___23_7113 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7130 -> HeadMatch false
  
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
          let uu____7152 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7152 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7163 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7187 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7197 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7224 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7224
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7225 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7226 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7227 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7240 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7254 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7278) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7284,uu____7285) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7327) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7352;
             FStar_Syntax_Syntax.index = uu____7353;
             FStar_Syntax_Syntax.sort = t2;_},uu____7355)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7363 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7364 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7365 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7380 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7387 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7407 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7407
  
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
           { FStar_Syntax_Syntax.blob = uu____7426;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7427;
             FStar_Syntax_Syntax.ltyp = uu____7428;
             FStar_Syntax_Syntax.rng = uu____7429;_},uu____7430)
            ->
            let uu____7441 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7441 t21
        | (uu____7442,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7443;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7444;
             FStar_Syntax_Syntax.ltyp = uu____7445;
             FStar_Syntax_Syntax.rng = uu____7446;_})
            ->
            let uu____7457 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7457
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7469 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7469
            then FullMatch
            else
              (let uu____7474 =
                 let uu____7483 =
                   let uu____7486 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7486  in
                 let uu____7487 =
                   let uu____7490 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7490  in
                 (uu____7483, uu____7487)  in
               MisMatch uu____7474)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7496),FStar_Syntax_Syntax.Tm_uinst (g,uu____7498)) ->
            let uu____7507 = head_matches env f g  in
            FStar_All.pipe_right uu____7507 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7508) -> HeadMatch true
        | (uu____7510,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7514 = FStar_Const.eq_const c d  in
            if uu____7514
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7524),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7526)) ->
            let uu____7559 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7559
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7569),FStar_Syntax_Syntax.Tm_refine (y,uu____7571)) ->
            let uu____7580 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7580 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7582),uu____7583) ->
            let uu____7588 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7588 head_match
        | (uu____7589,FStar_Syntax_Syntax.Tm_refine (x,uu____7591)) ->
            let uu____7596 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7596 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7597,FStar_Syntax_Syntax.Tm_type
           uu____7598) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7600,FStar_Syntax_Syntax.Tm_arrow uu____7601) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7632),FStar_Syntax_Syntax.Tm_app (head',uu____7634))
            ->
            let uu____7683 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7683 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7685),uu____7686) ->
            let uu____7711 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7711 head_match
        | (uu____7712,FStar_Syntax_Syntax.Tm_app (head1,uu____7714)) ->
            let uu____7739 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7739 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7740,FStar_Syntax_Syntax.Tm_let
           uu____7741) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7769,FStar_Syntax_Syntax.Tm_match uu____7770) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7816,FStar_Syntax_Syntax.Tm_abs
           uu____7817) -> HeadMatch true
        | uu____7855 ->
            let uu____7860 =
              let uu____7869 = delta_depth_of_term env t11  in
              let uu____7872 = delta_depth_of_term env t21  in
              (uu____7869, uu____7872)  in
            MisMatch uu____7860
  
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
              let uu____7941 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7941  in
            (let uu____7943 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7943
             then
               let uu____7948 = FStar_Syntax_Print.term_to_string t  in
               let uu____7950 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7948 uu____7950
             else ());
            (let uu____7955 =
               let uu____7956 = FStar_Syntax_Util.un_uinst head1  in
               uu____7956.FStar_Syntax_Syntax.n  in
             match uu____7955 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7962 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7962 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7976 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7976
                        then
                          let uu____7981 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7981
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7986 ->
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
                      let uu____8004 =
                        let uu____8006 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8006 = FStar_Syntax_Util.Equal  in
                      if uu____8004
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8013 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8013
                          then
                            let uu____8018 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8020 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8018
                              uu____8020
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8025 -> FStar_Pervasives_Native.None)
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
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8177 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8177
             then
               let uu____8182 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8184 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8186 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8182
                 uu____8184 uu____8186
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8214 =
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
               match uu____8214 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8262 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8262 with
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
                   aux retry (n_delta + Prims.int_one) t12 t22
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
                  uu____8300),uu____8301)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8322 =
                      let uu____8331 = maybe_inline t11  in
                      let uu____8334 = maybe_inline t21  in
                      (uu____8331, uu____8334)  in
                    match uu____8322 with
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
                 (uu____8377,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8378))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8399 =
                      let uu____8408 = maybe_inline t11  in
                      let uu____8411 = maybe_inline t21  in
                      (uu____8408, uu____8411)  in
                    match uu____8399 with
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
             | MisMatch uu____8466 -> fail1 n_delta r t11 t21
             | uu____8475 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8490 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8490
           then
             let uu____8495 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8497 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8499 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8507 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8524 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8524
                    (fun uu____8559  ->
                       match uu____8559 with
                       | (t11,t21) ->
                           let uu____8567 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8569 =
                             let uu____8571 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8571  in
                           Prims.op_Hat uu____8567 uu____8569))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8495 uu____8497 uu____8499 uu____8507
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8588 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8588 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8603  ->
    match uu___24_8603 with
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
      let uu___1221_8652 = p  in
      let uu____8655 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8656 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1221_8652.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8655;
        FStar_TypeChecker_Common.relation =
          (uu___1221_8652.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8656;
        FStar_TypeChecker_Common.element =
          (uu___1221_8652.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1221_8652.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1221_8652.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1221_8652.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1221_8652.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1221_8652.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8671 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8671
            (fun _8676  -> FStar_TypeChecker_Common.TProb _8676)
      | FStar_TypeChecker_Common.CProb uu____8677 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8700 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8700 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8708 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8708 with
           | (lh,lhs_args) ->
               let uu____8755 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8755 with
                | (rh,rhs_args) ->
                    let uu____8802 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8815,FStar_Syntax_Syntax.Tm_uvar uu____8816)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8905 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8932,uu____8933)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8948,FStar_Syntax_Syntax.Tm_uvar uu____8949)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8964,FStar_Syntax_Syntax.Tm_arrow uu____8965)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_8995 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_8995.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_8995.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_8995.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_8995.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_8995.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_8995.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_8995.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_8995.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_8995.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8998,FStar_Syntax_Syntax.Tm_type uu____8999)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_9015 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_9015.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_9015.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_9015.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_9015.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_9015.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_9015.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_9015.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_9015.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_9015.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9018,FStar_Syntax_Syntax.Tm_uvar uu____9019)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1272_9035 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1272_9035.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1272_9035.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1272_9035.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1272_9035.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1272_9035.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1272_9035.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1272_9035.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1272_9035.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1272_9035.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9038,FStar_Syntax_Syntax.Tm_uvar uu____9039)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9054,uu____9055)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9070,FStar_Syntax_Syntax.Tm_uvar uu____9071)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9086,uu____9087) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8802 with
                     | (rank,tp1) ->
                         let uu____9100 =
                           FStar_All.pipe_right
                             (let uu___1292_9104 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1292_9104.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1292_9104.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1292_9104.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1292_9104.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1292_9104.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1292_9104.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1292_9104.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1292_9104.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1292_9104.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9107  ->
                                FStar_TypeChecker_Common.TProb _9107)
                            in
                         (rank, uu____9100))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9111 =
            FStar_All.pipe_right
              (let uu___1296_9115 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1296_9115.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1296_9115.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1296_9115.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1296_9115.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1296_9115.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1296_9115.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1296_9115.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1296_9115.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1296_9115.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9118  -> FStar_TypeChecker_Common.CProb _9118)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9111)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9178 probs =
      match uu____9178 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9259 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9280 = rank wl.tcenv hd1  in
               (match uu____9280 with
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
                      (let uu____9341 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9346 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9346)
                          in
                       if uu____9341
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
          let uu____9419 = FStar_Syntax_Util.head_and_args t  in
          match uu____9419 with
          | (hd1,uu____9438) ->
              let uu____9463 =
                let uu____9464 = FStar_Syntax_Subst.compress hd1  in
                uu____9464.FStar_Syntax_Syntax.n  in
              (match uu____9463 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9469) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9504  ->
                           match uu____9504 with
                           | (y,uu____9513) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9536  ->
                                       match uu____9536 with
                                       | (x,uu____9545) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9550 -> false)
           in
        let uu____9552 = rank tcenv p  in
        match uu____9552 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9561 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9616 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9635 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9654 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9671 = FStar_Thunk.mkv s  in UFailed uu____9671 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9686 = FStar_Thunk.mk s  in UFailed uu____9686 
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
                        let uu____9738 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9738 with
                        | (k,uu____9746) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9759 -> false)))
            | uu____9761 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9813 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9821 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9821 = Prims.int_zero))
                           in
                        if uu____9813 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9842 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9850 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9850 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9842)
               in
            let uu____9854 = filter1 u12  in
            let uu____9857 = filter1 u22  in (uu____9854, uu____9857)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9892 = filter_out_common_univs us1 us2  in
                   (match uu____9892 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9952 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9952 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9955 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9972  ->
                               let uu____9973 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9975 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9973 uu____9975))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10001 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10001 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10027 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10027 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10030 ->
                   ufailed_thunk
                     (fun uu____10041  ->
                        let uu____10042 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10044 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10042 uu____10044 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10047,uu____10048) ->
              let uu____10050 =
                let uu____10052 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10054 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10052 uu____10054
                 in
              failwith uu____10050
          | (FStar_Syntax_Syntax.U_unknown ,uu____10057) ->
              let uu____10058 =
                let uu____10060 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10062 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10060 uu____10062
                 in
              failwith uu____10058
          | (uu____10065,FStar_Syntax_Syntax.U_bvar uu____10066) ->
              let uu____10068 =
                let uu____10070 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10072 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10070 uu____10072
                 in
              failwith uu____10068
          | (uu____10075,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10076 =
                let uu____10078 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10080 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10078 uu____10080
                 in
              failwith uu____10076
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10110 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10110
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10127 = occurs_univ v1 u3  in
              if uu____10127
              then
                let uu____10130 =
                  let uu____10132 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10134 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10132 uu____10134
                   in
                try_umax_components u11 u21 uu____10130
              else
                (let uu____10139 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10139)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10151 = occurs_univ v1 u3  in
              if uu____10151
              then
                let uu____10154 =
                  let uu____10156 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10158 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10156 uu____10158
                   in
                try_umax_components u11 u21 uu____10154
              else
                (let uu____10163 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10163)
          | (FStar_Syntax_Syntax.U_max uu____10164,uu____10165) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10173 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10173
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10179,FStar_Syntax_Syntax.U_max uu____10180) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10188 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10188
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10194,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10196,FStar_Syntax_Syntax.U_name uu____10197) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10199) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10201) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10203,FStar_Syntax_Syntax.U_succ uu____10204) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10206,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10313 = bc1  in
      match uu____10313 with
      | (bs1,mk_cod1) ->
          let uu____10357 = bc2  in
          (match uu____10357 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10468 = aux xs ys  in
                     (match uu____10468 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10551 =
                       let uu____10558 = mk_cod1 xs  in ([], uu____10558)  in
                     let uu____10561 =
                       let uu____10568 = mk_cod2 ys  in ([], uu____10568)  in
                     (uu____10551, uu____10561)
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
                  let uu____10637 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10637 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10640 =
                    let uu____10641 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10641 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10640
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10646 = has_type_guard t1 t2  in (uu____10646, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10647 = has_type_guard t2 t1  in (uu____10647, wl)
  
let is_flex_pat :
  'Auu____10657 'Auu____10658 'Auu____10659 .
    ('Auu____10657 * 'Auu____10658 * 'Auu____10659 Prims.list) -> Prims.bool
  =
  fun uu___25_10673  ->
    match uu___25_10673 with
    | (uu____10682,uu____10683,[]) -> true
    | uu____10687 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10720 = f  in
      match uu____10720 with
      | (uu____10727,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10728;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10729;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10732;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10733;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10734;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10735;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10805  ->
                 match uu____10805 with
                 | (y,uu____10814) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10968 =
                  let uu____10983 =
                    let uu____10986 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____10986  in
                  ((FStar_List.rev pat_binders), uu____10983)  in
                FStar_Pervasives_Native.Some uu____10968
            | (uu____11019,[]) ->
                let uu____11050 =
                  let uu____11065 =
                    let uu____11068 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11068  in
                  ((FStar_List.rev pat_binders), uu____11065)  in
                FStar_Pervasives_Native.Some uu____11050
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11159 =
                  let uu____11160 = FStar_Syntax_Subst.compress a  in
                  uu____11160.FStar_Syntax_Syntax.n  in
                (match uu____11159 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11180 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11180
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1624_11210 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1624_11210.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1624_11210.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11214 =
                            let uu____11215 =
                              let uu____11222 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11222)  in
                            FStar_Syntax_Syntax.NT uu____11215  in
                          [uu____11214]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1630_11238 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1630_11238.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1630_11238.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11239 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11279 =
                  let uu____11294 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11294  in
                (match uu____11279 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11369 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11402 ->
               let uu____11403 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11403 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11723 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11723
       then
         let uu____11728 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11728
       else ());
      (let uu____11733 = next_prob probs  in
       match uu____11733 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1655_11760 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1655_11760.wl_deferred);
               ctr = (uu___1655_11760.ctr);
               defer_ok = (uu___1655_11760.defer_ok);
               smt_ok = (uu___1655_11760.smt_ok);
               umax_heuristic_ok = (uu___1655_11760.umax_heuristic_ok);
               tcenv = (uu___1655_11760.tcenv);
               wl_implicits = (uu___1655_11760.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11769 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11769
                 then
                   let uu____11772 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11772
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
                       (let uu____11779 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11779)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1667_11785 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1667_11785.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1667_11785.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1667_11785.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1667_11785.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1667_11785.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1667_11785.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1667_11785.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1667_11785.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1667_11785.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11810 ->
                let uu____11820 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11885  ->
                          match uu____11885 with
                          | (c,uu____11895,uu____11896) -> c < probs.ctr))
                   in
                (match uu____11820 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11944 =
                            let uu____11949 =
                              FStar_List.map
                                (fun uu____11970  ->
                                   match uu____11970 with
                                   | (uu____11986,x,y) ->
                                       let uu____11997 = FStar_Thunk.force x
                                          in
                                       (uu____11997, y)) probs.wl_deferred
                               in
                            (uu____11949, (probs.wl_implicits))  in
                          Success uu____11944
                      | uu____12001 ->
                          let uu____12011 =
                            let uu___1685_12012 = probs  in
                            let uu____12013 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12034  ->
                                      match uu____12034 with
                                      | (uu____12042,uu____12043,y) -> y))
                               in
                            {
                              attempting = uu____12013;
                              wl_deferred = rest;
                              ctr = (uu___1685_12012.ctr);
                              defer_ok = (uu___1685_12012.defer_ok);
                              smt_ok = (uu___1685_12012.smt_ok);
                              umax_heuristic_ok =
                                (uu___1685_12012.umax_heuristic_ok);
                              tcenv = (uu___1685_12012.tcenv);
                              wl_implicits = (uu___1685_12012.wl_implicits)
                            }  in
                          solve env uu____12011))))

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
            let uu____12052 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12052 with
            | USolved wl1 ->
                let uu____12054 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12054
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12057 = defer_lit "" orig wl1  in
                solve env uu____12057

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
                  let uu____12108 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12108 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12111 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12124;
                  FStar_Syntax_Syntax.vars = uu____12125;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12128;
                  FStar_Syntax_Syntax.vars = uu____12129;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12142,uu____12143) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12151,FStar_Syntax_Syntax.Tm_uinst uu____12152) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12160 -> USolved wl

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
            ((let uu____12171 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12171
              then
                let uu____12176 = prob_to_string env orig  in
                let uu____12178 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12176 uu____12178
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
               let uu____12271 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12271 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12326 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12326
                then
                  let uu____12331 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12333 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12331 uu____12333
                else ());
               (let uu____12338 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12338 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12384 = eq_prob t1 t2 wl2  in
                         (match uu____12384 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12405 ->
                         let uu____12414 = eq_prob t1 t2 wl2  in
                         (match uu____12414 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12464 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12479 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12480 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12479, uu____12480)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12485 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12486 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12485, uu____12486)
                            in
                         (match uu____12464 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12517 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12517 with
                                | (t1_hd,t1_args) ->
                                    let uu____12562 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12562 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12628 =
                                              let uu____12635 =
                                                let uu____12646 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12646 :: t1_args  in
                                              let uu____12663 =
                                                let uu____12672 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12672 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12721  ->
                                                   fun uu____12722  ->
                                                     fun uu____12723  ->
                                                       match (uu____12721,
                                                               uu____12722,
                                                               uu____12723)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12773),
                                                          (a2,uu____12775))
                                                           ->
                                                           let uu____12812 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12812
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12635
                                                uu____12663
                                               in
                                            match uu____12628 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1839_12838 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1839_12838.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1839_12838.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1839_12838.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12849 =
                                                  solve env1 wl'  in
                                                (match uu____12849 with
                                                 | Success (uu____12852,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1848_12856
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1848_12856.attempting);
                                                            wl_deferred =
                                                              (uu___1848_12856.wl_deferred);
                                                            ctr =
                                                              (uu___1848_12856.ctr);
                                                            defer_ok =
                                                              (uu___1848_12856.defer_ok);
                                                            smt_ok =
                                                              (uu___1848_12856.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1848_12856.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1848_12856.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12857 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12889 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12889 with
                                | (t1_base,p1_opt) ->
                                    let uu____12925 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12925 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13024 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13024
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
                                               let uu____13077 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13077
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
                                               let uu____13109 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13109
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
                                               let uu____13141 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13141
                                           | uu____13144 -> t_base  in
                                         let uu____13161 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13161 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13175 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13175, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13182 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13182 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13218 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13218 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13254 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13254
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
                              let uu____13278 = combine t11 t21 wl2  in
                              (match uu____13278 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13311 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13311
                                     then
                                       let uu____13316 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13316
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13358 ts1 =
               match uu____13358 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13421 = pairwise out t wl2  in
                        (match uu____13421 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13457 =
               let uu____13468 = FStar_List.hd ts  in (uu____13468, [], wl1)
                in
             let uu____13477 = FStar_List.tl ts  in
             aux uu____13457 uu____13477  in
           let uu____13484 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13484 with
           | (this_flex,this_rigid) ->
               let uu____13510 =
                 let uu____13511 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13511.FStar_Syntax_Syntax.n  in
               (match uu____13510 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13536 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13536
                    then
                      let uu____13539 = destruct_flex_t this_flex wl  in
                      (match uu____13539 with
                       | (flex,wl1) ->
                           let uu____13546 = quasi_pattern env flex  in
                           (match uu____13546 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13565 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13565
                                  then
                                    let uu____13570 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13570
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13577 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1950_13580 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1950_13580.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1950_13580.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1950_13580.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1950_13580.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1950_13580.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1950_13580.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1950_13580.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1950_13580.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1950_13580.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13577)
                | uu____13581 ->
                    ((let uu____13583 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13583
                      then
                        let uu____13588 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13588
                      else ());
                     (let uu____13593 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13593 with
                      | (u,_args) ->
                          let uu____13636 =
                            let uu____13637 = FStar_Syntax_Subst.compress u
                               in
                            uu____13637.FStar_Syntax_Syntax.n  in
                          (match uu____13636 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13665 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13665 with
                                 | (u',uu____13684) ->
                                     let uu____13709 =
                                       let uu____13710 = whnf env u'  in
                                       uu____13710.FStar_Syntax_Syntax.n  in
                                     (match uu____13709 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13732 -> false)
                                  in
                               let uu____13734 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13757  ->
                                         match uu___26_13757 with
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
                                              | uu____13771 -> false)
                                         | uu____13775 -> false))
                                  in
                               (match uu____13734 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13790 = whnf env this_rigid
                                         in
                                      let uu____13791 =
                                        FStar_List.collect
                                          (fun uu___27_13797  ->
                                             match uu___27_13797 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13803 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13803]
                                             | uu____13807 -> [])
                                          bounds_probs
                                         in
                                      uu____13790 :: uu____13791  in
                                    let uu____13808 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13808 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13841 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13856 =
                                               let uu____13857 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13857.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13856 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13869 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13869)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13880 -> bound  in
                                           let uu____13881 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13881)  in
                                         (match uu____13841 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13916 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13916
                                                then
                                                  let wl'1 =
                                                    let uu___2010_13922 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2010_13922.wl_deferred);
                                                      ctr =
                                                        (uu___2010_13922.ctr);
                                                      defer_ok =
                                                        (uu___2010_13922.defer_ok);
                                                      smt_ok =
                                                        (uu___2010_13922.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2010_13922.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2010_13922.tcenv);
                                                      wl_implicits =
                                                        (uu___2010_13922.wl_implicits)
                                                    }  in
                                                  let uu____13923 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13923
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13929 =
                                                  solve_t env eq_prob
                                                    (let uu___2015_13931 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2015_13931.wl_deferred);
                                                       ctr =
                                                         (uu___2015_13931.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2015_13931.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2015_13931.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2015_13931.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13929 with
                                                | Success (uu____13933,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2021_13936 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2021_13936.wl_deferred);
                                                        ctr =
                                                          (uu___2021_13936.ctr);
                                                        defer_ok =
                                                          (uu___2021_13936.defer_ok);
                                                        smt_ok =
                                                          (uu___2021_13936.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2021_13936.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2021_13936.tcenv);
                                                        wl_implicits =
                                                          (uu___2021_13936.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2024_13938 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2024_13938.attempting);
                                                        wl_deferred =
                                                          (uu___2024_13938.wl_deferred);
                                                        ctr =
                                                          (uu___2024_13938.ctr);
                                                        defer_ok =
                                                          (uu___2024_13938.defer_ok);
                                                        smt_ok =
                                                          (uu___2024_13938.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2024_13938.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2024_13938.tcenv);
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
                                                    let uu____13954 =
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
                                                    ((let uu____13966 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13966
                                                      then
                                                        let uu____13971 =
                                                          let uu____13973 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13973
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13971
                                                      else ());
                                                     (let uu____13986 =
                                                        let uu____14001 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14001)
                                                         in
                                                      match uu____13986 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14023))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14049 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14049
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
                                                                  let uu____14069
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14069))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14094 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14094
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
                                                                    let uu____14114
                                                                    =
                                                                    let uu____14119
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14119
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14114
                                                                    [] wl2
                                                                     in
                                                                  let uu____14125
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14125))))
                                                      | uu____14126 ->
                                                          let uu____14141 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14141 p)))))))
                           | uu____14148 when flip ->
                               let uu____14149 =
                                 let uu____14151 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14153 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14151 uu____14153
                                  in
                               failwith uu____14149
                           | uu____14156 ->
                               let uu____14157 =
                                 let uu____14159 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14161 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14159 uu____14161
                                  in
                               failwith uu____14157)))))

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
                      (fun uu____14197  ->
                         match uu____14197 with
                         | (x,i) ->
                             let uu____14216 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14216, i)) bs_lhs
                     in
                  let uu____14219 = lhs  in
                  match uu____14219 with
                  | (uu____14220,u_lhs,uu____14222) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14319 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14329 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14329, univ)
                             in
                          match uu____14319 with
                          | (k,univ) ->
                              let uu____14336 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14336 with
                               | (uu____14353,u,wl3) ->
                                   let uu____14356 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14356, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14382 =
                              let uu____14395 =
                                let uu____14406 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14406 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14457  ->
                                   fun uu____14458  ->
                                     match (uu____14457, uu____14458) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14559 =
                                           let uu____14566 =
                                             let uu____14569 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14569
                                              in
                                           copy_uvar u_lhs [] uu____14566 wl2
                                            in
                                         (match uu____14559 with
                                          | (uu____14598,t_a,wl3) ->
                                              let uu____14601 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14601 with
                                               | (uu____14620,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14395
                                ([], wl1)
                               in
                            (match uu____14382 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2135_14676 = ct  in
                                   let uu____14677 =
                                     let uu____14680 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14680
                                      in
                                   let uu____14695 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2135_14676.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2135_14676.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14677;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14695;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2135_14676.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2138_14713 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2138_14713.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2138_14713.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14716 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14716 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14778 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14778 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14789 =
                                          let uu____14794 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14794)  in
                                        TERM uu____14789  in
                                      let uu____14795 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14795 with
                                       | (sub_prob,wl3) ->
                                           let uu____14809 =
                                             let uu____14810 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14810
                                              in
                                           solve env uu____14809))
                             | (x,imp)::formals2 ->
                                 let uu____14832 =
                                   let uu____14839 =
                                     let uu____14842 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14842
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14839 wl1
                                    in
                                 (match uu____14832 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14863 =
                                          let uu____14866 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14866
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14863 u_x
                                         in
                                      let uu____14867 =
                                        let uu____14870 =
                                          let uu____14873 =
                                            let uu____14874 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14874, imp)  in
                                          [uu____14873]  in
                                        FStar_List.append bs_terms
                                          uu____14870
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14867 formals2 wl2)
                              in
                           let uu____14901 = occurs_check u_lhs arrow1  in
                           (match uu____14901 with
                            | (uu____14914,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14930 =
                                    FStar_Thunk.mk
                                      (fun uu____14934  ->
                                         let uu____14935 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14935)
                                     in
                                  giveup_or_defer env orig wl uu____14930
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
              (let uu____14968 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14968
               then
                 let uu____14973 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14976 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14973 (rel_to_string (p_rel orig)) uu____14976
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15107 = rhs wl1 scope env1 subst1  in
                     (match uu____15107 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15130 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15130
                            then
                              let uu____15135 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15135
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15213 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15213 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2208_15215 = hd1  in
                       let uu____15216 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2208_15215.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2208_15215.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15216
                       }  in
                     let hd21 =
                       let uu___2211_15220 = hd2  in
                       let uu____15221 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2211_15220.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2211_15220.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15221
                       }  in
                     let uu____15224 =
                       let uu____15229 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15229
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15224 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15252 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15252
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15259 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15259 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15331 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15331
                                  in
                               ((let uu____15349 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15349
                                 then
                                   let uu____15354 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15356 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15354
                                     uu____15356
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15391 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15427 = aux wl [] env [] bs1 bs2  in
               match uu____15427 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15486 = attempt sub_probs wl2  in
                   solve env1 uu____15486)

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
            let uu___2249_15506 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2249_15506.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2249_15506.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15518 = try_solve env wl'  in
          match uu____15518 with
          | Success (uu____15519,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2258_15523 = wl  in
                  {
                    attempting = (uu___2258_15523.attempting);
                    wl_deferred = (uu___2258_15523.wl_deferred);
                    ctr = (uu___2258_15523.ctr);
                    defer_ok = (uu___2258_15523.defer_ok);
                    smt_ok = (uu___2258_15523.smt_ok);
                    umax_heuristic_ok = (uu___2258_15523.umax_heuristic_ok);
                    tcenv = (uu___2258_15523.tcenv);
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
        (let uu____15532 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15532 wl)

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
              let uu____15546 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15546 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15580 = lhs1  in
              match uu____15580 with
              | (uu____15583,ctx_u,uu____15585) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15593 ->
                        let uu____15594 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15594 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15643 = quasi_pattern env1 lhs1  in
              match uu____15643 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15677) ->
                  let uu____15682 = lhs1  in
                  (match uu____15682 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15697 = occurs_check ctx_u rhs1  in
                       (match uu____15697 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15748 =
                                let uu____15756 =
                                  let uu____15758 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15758
                                   in
                                FStar_Util.Inl uu____15756  in
                              (uu____15748, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15786 =
                                 let uu____15788 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15788  in
                               if uu____15786
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15815 =
                                    let uu____15823 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15823  in
                                  let uu____15829 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15815, uu____15829)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15873 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15873 with
              | (rhs_hd,args) ->
                  let uu____15916 = FStar_Util.prefix args  in
                  (match uu____15916 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15988 = lhs1  in
                       (match uu____15988 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15992 =
                              let uu____16003 =
                                let uu____16010 =
                                  let uu____16013 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____16013
                                   in
                                copy_uvar u_lhs [] uu____16010 wl1  in
                              match uu____16003 with
                              | (uu____16040,t_last_arg,wl2) ->
                                  let uu____16043 =
                                    let uu____16050 =
                                      let uu____16051 =
                                        let uu____16060 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16060]  in
                                      FStar_List.append bs_lhs uu____16051
                                       in
                                    copy_uvar u_lhs uu____16050 t_res_lhs wl2
                                     in
                                  (match uu____16043 with
                                   | (uu____16095,lhs',wl3) ->
                                       let uu____16098 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16098 with
                                        | (uu____16115,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15992 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16136 =
                                     let uu____16137 =
                                       let uu____16142 =
                                         let uu____16143 =
                                           let uu____16146 =
                                             let uu____16151 =
                                               let uu____16152 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16152]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16151
                                              in
                                           uu____16146
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16143
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16142)  in
                                     TERM uu____16137  in
                                   [uu____16136]  in
                                 let uu____16177 =
                                   let uu____16184 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16184 with
                                   | (p1,wl3) ->
                                       let uu____16204 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16204 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16177 with
                                  | (sub_probs,wl3) ->
                                      let uu____16236 =
                                        let uu____16237 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16237  in
                                      solve env1 uu____16236))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16271 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16271 with
                | (uu____16289,args) ->
                    (match args with | [] -> false | uu____16325 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16344 =
                  let uu____16345 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16345.FStar_Syntax_Syntax.n  in
                match uu____16344 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16349 -> true
                | uu____16365 -> false  in
              let uu____16367 = quasi_pattern env1 lhs1  in
              match uu____16367 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    FStar_Thunk.mk
                      (fun uu____16385  ->
                         let uu____16386 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16386)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16395 = is_app rhs1  in
                  if uu____16395
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16400 = is_arrow rhs1  in
                     if uu____16400
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          FStar_Thunk.mk
                            (fun uu____16412  ->
                               let uu____16413 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16413)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16417 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16417
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16423 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16423
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16428 = lhs  in
                (match uu____16428 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16432 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16432 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16450 =
                              let uu____16454 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16454
                               in
                            FStar_All.pipe_right uu____16450
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16475 = occurs_check ctx_uv rhs1  in
                          (match uu____16475 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16504 =
                                   let uu____16505 =
                                     let uu____16507 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16507
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16505
                                    in
                                 giveup_or_defer env orig wl uu____16504
                               else
                                 (let uu____16515 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16515
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16522 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16522
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         FStar_Thunk.mk
                                           (fun uu____16535  ->
                                              let uu____16536 =
                                                names_to_string1 fvs2  in
                                              let uu____16538 =
                                                names_to_string1 fvs1  in
                                              let uu____16540 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16536 uu____16538
                                                uu____16540)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16552 ->
                          if wl.defer_ok
                          then
                            let uu____16556 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16556
                          else
                            (let uu____16561 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16561 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16587 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16587
                             | (FStar_Util.Inl msg,uu____16589) ->
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
                  let uu____16607 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16607
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16613 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16613
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16635 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16635
                else
                  (let uu____16640 =
                     let uu____16657 = quasi_pattern env lhs  in
                     let uu____16664 = quasi_pattern env rhs  in
                     (uu____16657, uu____16664)  in
                   match uu____16640 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16707 = lhs  in
                       (match uu____16707 with
                        | ({ FStar_Syntax_Syntax.n = uu____16708;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16710;_},u_lhs,uu____16712)
                            ->
                            let uu____16715 = rhs  in
                            (match uu____16715 with
                             | (uu____16716,u_rhs,uu____16718) ->
                                 let uu____16719 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16719
                                 then
                                   let uu____16726 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16726
                                 else
                                   (let uu____16729 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16729 with
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
                                        let uu____16761 =
                                          let uu____16768 =
                                            let uu____16771 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16771
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16768
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16761 with
                                         | (uu____16783,w,wl1) ->
                                             let w_app =
                                               let uu____16789 =
                                                 let uu____16794 =
                                                   FStar_List.map
                                                     (fun uu____16805  ->
                                                        match uu____16805
                                                        with
                                                        | (z,uu____16813) ->
                                                            let uu____16818 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16818) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16794
                                                  in
                                               uu____16789
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16820 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16820
                                               then
                                                 let uu____16825 =
                                                   let uu____16829 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16831 =
                                                     let uu____16835 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16837 =
                                                       let uu____16841 =
                                                         term_to_string w  in
                                                       let uu____16843 =
                                                         let uu____16847 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16856 =
                                                           let uu____16860 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16869 =
                                                             let uu____16873
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16873]
                                                              in
                                                           uu____16860 ::
                                                             uu____16869
                                                            in
                                                         uu____16847 ::
                                                           uu____16856
                                                          in
                                                       uu____16841 ::
                                                         uu____16843
                                                        in
                                                     uu____16835 ::
                                                       uu____16837
                                                      in
                                                   uu____16829 :: uu____16831
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16825
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16890 =
                                                     let uu____16895 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16895)  in
                                                   TERM uu____16890  in
                                                 let uu____16896 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16896
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16904 =
                                                        let uu____16909 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16909)
                                                         in
                                                      TERM uu____16904  in
                                                    [s1; s2])
                                                  in
                                               let uu____16910 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16910))))))
                   | uu____16911 ->
                       let uu____16928 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16928)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16982 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16982
            then
              let uu____16987 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16989 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16991 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16993 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16987 uu____16989 uu____16991 uu____16993
            else ());
           (let uu____17004 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17004 with
            | (head1,args1) ->
                let uu____17047 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17047 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17117 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17117 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17122 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17122)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17143 =
                         FStar_Thunk.mk
                           (fun uu____17150  ->
                              let uu____17151 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17153 = args_to_string args1  in
                              let uu____17157 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17159 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17151 uu____17153 uu____17157
                                uu____17159)
                          in
                       giveup env1 uu____17143 orig
                     else
                       (let uu____17166 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17171 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17171 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17166
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2514_17175 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2514_17175.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2514_17175.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2514_17175.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2514_17175.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2514_17175.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2514_17175.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2514_17175.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2514_17175.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17185 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17185
                                    else solve env1 wl2))
                        else
                          (let uu____17190 = base_and_refinement env1 t1  in
                           match uu____17190 with
                           | (base1,refinement1) ->
                               let uu____17215 = base_and_refinement env1 t2
                                  in
                               (match uu____17215 with
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
                                           let uu____17380 =
                                             FStar_List.fold_right
                                               (fun uu____17420  ->
                                                  fun uu____17421  ->
                                                    match (uu____17420,
                                                            uu____17421)
                                                    with
                                                    | (((a1,uu____17473),
                                                        (a2,uu____17475)),
                                                       (probs,wl3)) ->
                                                        let uu____17524 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17524
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17380 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17567 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17567
                                                 then
                                                   let uu____17572 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17572
                                                 else ());
                                                (let uu____17578 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17578
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
                                                    (let uu____17605 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17605 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17621 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17621
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17629 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17629))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17653 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17653 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____17667 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17667)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17695 =
                                           match uu____17695 with
                                           | (prob,reason) ->
                                               ((let uu____17712 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17712
                                                 then
                                                   let uu____17717 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17719 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____17721 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____17717 uu____17719
                                                     uu____17721
                                                 else ());
                                                (let uu____17727 =
                                                   let uu____17736 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17739 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17736, uu____17739)
                                                    in
                                                 match uu____17727 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17752 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17752 with
                                                      | (head1',uu____17770)
                                                          ->
                                                          let uu____17795 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17795
                                                           with
                                                           | (head2',uu____17813)
                                                               ->
                                                               let uu____17838
                                                                 =
                                                                 let uu____17843
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17844
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17843,
                                                                   uu____17844)
                                                                  in
                                                               (match uu____17838
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17846
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17846
                                                                    then
                                                                    let uu____17851
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17853
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17855
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17857
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17851
                                                                    uu____17853
                                                                    uu____17855
                                                                    uu____17857
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17862
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2600_17870
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2600_17870.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17872
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17872
                                                                    then
                                                                    let uu____17877
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17877
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17882 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17894 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17894 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17902 =
                                             let uu____17903 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17903.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17902 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17908 -> false  in
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
                                          | uu____17911 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17914 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2620_17950 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2620_17950.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2620_17950.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2620_17950.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2620_17950.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2620_17950.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2620_17950.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2620_17950.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2620_17950.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18026 = destruct_flex_t scrutinee wl1  in
             match uu____18026 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18037 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18037 with
                  | (xs,pat_term,uu____18053,uu____18054) ->
                      let uu____18059 =
                        FStar_List.fold_left
                          (fun uu____18082  ->
                             fun x  ->
                               match uu____18082 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18103 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18103 with
                                    | (uu____18122,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18059 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18143 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18143 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2660_18160 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2660_18160.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2660_18160.umax_heuristic_ok);
                                    tcenv = (uu___2660_18160.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18171 = solve env1 wl'  in
                                (match uu____18171 with
                                 | Success (uu____18174,imps) ->
                                     let wl'1 =
                                       let uu___2668_18177 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2668_18177.wl_deferred);
                                         ctr = (uu___2668_18177.ctr);
                                         defer_ok =
                                           (uu___2668_18177.defer_ok);
                                         smt_ok = (uu___2668_18177.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2668_18177.umax_heuristic_ok);
                                         tcenv = (uu___2668_18177.tcenv);
                                         wl_implicits =
                                           (uu___2668_18177.wl_implicits)
                                       }  in
                                     let uu____18178 = solve env1 wl'1  in
                                     (match uu____18178 with
                                      | Success (uu____18181,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2676_18185 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2676_18185.attempting);
                                                 wl_deferred =
                                                   (uu___2676_18185.wl_deferred);
                                                 ctr = (uu___2676_18185.ctr);
                                                 defer_ok =
                                                   (uu___2676_18185.defer_ok);
                                                 smt_ok =
                                                   (uu___2676_18185.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2676_18185.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2676_18185.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18186 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18192 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18215 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18215
                 then
                   let uu____18220 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18222 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18220 uu____18222
                 else ());
                (let uu____18227 =
                   let uu____18248 =
                     let uu____18257 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18257)  in
                   let uu____18264 =
                     let uu____18273 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18273)  in
                   (uu____18248, uu____18264)  in
                 match uu____18227 with
                 | ((uu____18303,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18306;
                                   FStar_Syntax_Syntax.vars = uu____18307;_}),
                    (s,t)) ->
                     let uu____18378 =
                       let uu____18380 = is_flex scrutinee  in
                       Prims.op_Negation uu____18380  in
                     if uu____18378
                     then
                       ((let uu____18391 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18391
                         then
                           let uu____18396 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18396
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18415 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18415
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18430 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18430
                           then
                             let uu____18435 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18437 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18435 uu____18437
                           else ());
                          (let pat_discriminates uu___28_18462 =
                             match uu___28_18462 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18478;
                                  FStar_Syntax_Syntax.p = uu____18479;_},FStar_Pervasives_Native.None
                                ,uu____18480) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18494;
                                  FStar_Syntax_Syntax.p = uu____18495;_},FStar_Pervasives_Native.None
                                ,uu____18496) -> true
                             | uu____18523 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18626 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18626 with
                                       | (uu____18628,uu____18629,t') ->
                                           let uu____18647 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18647 with
                                            | (FullMatch ,uu____18659) ->
                                                true
                                            | (HeadMatch
                                               uu____18673,uu____18674) ->
                                                true
                                            | uu____18689 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18726 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18726
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18737 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18737 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18825,uu____18826) ->
                                       branches1
                                   | uu____18971 -> branches  in
                                 let uu____19026 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19035 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19035 with
                                        | (p,uu____19039,uu____19040) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19069  -> FStar_Util.Inr _19069)
                                   uu____19026))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19099 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19099 with
                                | (p,uu____19108,e) ->
                                    ((let uu____19127 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19127
                                      then
                                        let uu____19132 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19134 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19132 uu____19134
                                      else ());
                                     (let uu____19139 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19154  -> FStar_Util.Inr _19154)
                                        uu____19139)))))
                 | ((s,t),(uu____19157,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19160;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19161;_}))
                     ->
                     let uu____19230 =
                       let uu____19232 = is_flex scrutinee  in
                       Prims.op_Negation uu____19232  in
                     if uu____19230
                     then
                       ((let uu____19243 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19243
                         then
                           let uu____19248 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19248
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19267 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19267
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19282 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19282
                           then
                             let uu____19287 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19289 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19287 uu____19289
                           else ());
                          (let pat_discriminates uu___28_19314 =
                             match uu___28_19314 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19330;
                                  FStar_Syntax_Syntax.p = uu____19331;_},FStar_Pervasives_Native.None
                                ,uu____19332) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19346;
                                  FStar_Syntax_Syntax.p = uu____19347;_},FStar_Pervasives_Native.None
                                ,uu____19348) -> true
                             | uu____19375 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19478 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19478 with
                                       | (uu____19480,uu____19481,t') ->
                                           let uu____19499 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19499 with
                                            | (FullMatch ,uu____19511) ->
                                                true
                                            | (HeadMatch
                                               uu____19525,uu____19526) ->
                                                true
                                            | uu____19541 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19578 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19578
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19589 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19589 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19677,uu____19678) ->
                                       branches1
                                   | uu____19823 -> branches  in
                                 let uu____19878 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19887 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19887 with
                                        | (p,uu____19891,uu____19892) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19921  -> FStar_Util.Inr _19921)
                                   uu____19878))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19951 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19951 with
                                | (p,uu____19960,e) ->
                                    ((let uu____19979 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19979
                                      then
                                        let uu____19984 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19986 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19984 uu____19986
                                      else ());
                                     (let uu____19991 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20006  -> FStar_Util.Inr _20006)
                                        uu____19991)))))
                 | uu____20007 ->
                     ((let uu____20029 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20029
                       then
                         let uu____20034 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20036 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20034 uu____20036
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20082 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20082
            then
              let uu____20087 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20089 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20091 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20093 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20087 uu____20089 uu____20091 uu____20093
            else ());
           (let uu____20098 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20098 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20129,uu____20130) ->
                     let rec may_relate head3 =
                       let uu____20158 =
                         let uu____20159 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20159.FStar_Syntax_Syntax.n  in
                       match uu____20158 with
                       | FStar_Syntax_Syntax.Tm_name uu____20163 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20165 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20190 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20190 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20192 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20195
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20196 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20199,uu____20200) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20242) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20248) ->
                           may_relate t
                       | uu____20253 -> false  in
                     let uu____20255 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20255 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20268 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20268
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20278 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20278
                          then
                            let uu____20281 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20281 with
                             | (guard,wl2) ->
                                 let uu____20288 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20288)
                          else
                            (let uu____20291 =
                               FStar_Thunk.mk
                                 (fun uu____20298  ->
                                    let uu____20299 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20301 =
                                      let uu____20303 =
                                        let uu____20307 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20307
                                          (fun x  ->
                                             let uu____20314 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20314)
                                         in
                                      FStar_Util.dflt "" uu____20303  in
                                    let uu____20319 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20321 =
                                      let uu____20323 =
                                        let uu____20327 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20327
                                          (fun x  ->
                                             let uu____20334 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20334)
                                         in
                                      FStar_Util.dflt "" uu____20323  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20299 uu____20301 uu____20319
                                      uu____20321)
                                in
                             giveup env1 uu____20291 orig))
                 | (HeadMatch (true ),uu____20340) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20355 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20355 with
                        | (guard,wl2) ->
                            let uu____20362 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20362)
                     else
                       (let uu____20365 =
                          FStar_Thunk.mk
                            (fun uu____20370  ->
                               let uu____20371 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20373 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20371 uu____20373)
                           in
                        giveup env1 uu____20365 orig)
                 | (uu____20376,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2851_20390 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2851_20390.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2851_20390.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2851_20390.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2851_20390.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2851_20390.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2851_20390.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2851_20390.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2851_20390.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20417 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20417
          then
            let uu____20420 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20420
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20426 =
                let uu____20429 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20429  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20426 t1);
             (let uu____20448 =
                let uu____20451 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20451  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20448 t2);
             (let uu____20470 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20470
              then
                let uu____20474 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20476 =
                  let uu____20478 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20480 =
                    let uu____20482 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20482  in
                  Prims.op_Hat uu____20478 uu____20480  in
                let uu____20485 =
                  let uu____20487 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20489 =
                    let uu____20491 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20491  in
                  Prims.op_Hat uu____20487 uu____20489  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20474 uu____20476 uu____20485
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20498,uu____20499) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20523,FStar_Syntax_Syntax.Tm_delayed uu____20524) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20548,uu____20549) ->
                  let uu____20576 =
                    let uu___2882_20577 = problem  in
                    let uu____20578 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2882_20577.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20578;
                      FStar_TypeChecker_Common.relation =
                        (uu___2882_20577.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2882_20577.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2882_20577.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2882_20577.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2882_20577.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2882_20577.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2882_20577.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2882_20577.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20576 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20579,uu____20580) ->
                  let uu____20587 =
                    let uu___2888_20588 = problem  in
                    let uu____20589 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2888_20588.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20589;
                      FStar_TypeChecker_Common.relation =
                        (uu___2888_20588.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2888_20588.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2888_20588.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2888_20588.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2888_20588.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2888_20588.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2888_20588.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2888_20588.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20587 wl
              | (uu____20590,FStar_Syntax_Syntax.Tm_ascribed uu____20591) ->
                  let uu____20618 =
                    let uu___2894_20619 = problem  in
                    let uu____20620 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2894_20619.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2894_20619.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2894_20619.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20620;
                      FStar_TypeChecker_Common.element =
                        (uu___2894_20619.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2894_20619.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2894_20619.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2894_20619.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2894_20619.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2894_20619.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20618 wl
              | (uu____20621,FStar_Syntax_Syntax.Tm_meta uu____20622) ->
                  let uu____20629 =
                    let uu___2900_20630 = problem  in
                    let uu____20631 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2900_20630.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2900_20630.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2900_20630.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20631;
                      FStar_TypeChecker_Common.element =
                        (uu___2900_20630.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2900_20630.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2900_20630.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2900_20630.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2900_20630.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2900_20630.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20629 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20633),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20635)) ->
                  let uu____20644 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20644
              | (FStar_Syntax_Syntax.Tm_bvar uu____20645,uu____20646) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20648,FStar_Syntax_Syntax.Tm_bvar uu____20649) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20719 =
                    match uu___29_20719 with
                    | [] -> c
                    | bs ->
                        let uu____20747 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20747
                     in
                  let uu____20758 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20758 with
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
                                    let uu____20907 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20907
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
                  let mk_t t l uu___30_20996 =
                    match uu___30_20996 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21038 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21038 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21183 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21184 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21183
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21184 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21186,uu____21187) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21218 -> true
                    | uu____21238 -> false  in
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
                      (let uu____21298 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3002_21306 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3002_21306.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3002_21306.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3002_21306.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3002_21306.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3002_21306.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3002_21306.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3002_21306.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3002_21306.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3002_21306.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3002_21306.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3002_21306.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3002_21306.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3002_21306.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3002_21306.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3002_21306.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3002_21306.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3002_21306.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3002_21306.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3002_21306.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3002_21306.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3002_21306.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3002_21306.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3002_21306.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3002_21306.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3002_21306.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3002_21306.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3002_21306.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3002_21306.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3002_21306.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3002_21306.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3002_21306.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3002_21306.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3002_21306.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3002_21306.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3002_21306.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3002_21306.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3002_21306.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3002_21306.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3002_21306.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3002_21306.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3002_21306.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3002_21306.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21298 with
                       | (uu____21311,ty,uu____21313) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21322 =
                                 let uu____21323 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21323.FStar_Syntax_Syntax.n  in
                               match uu____21322 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21326 ->
                                   let uu____21333 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21333
                               | uu____21334 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21337 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21337
                             then
                               let uu____21342 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21344 =
                                 let uu____21346 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21346
                                  in
                               let uu____21347 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21342 uu____21344 uu____21347
                             else ());
                            r1))
                     in
                  let uu____21352 =
                    let uu____21369 = maybe_eta t1  in
                    let uu____21376 = maybe_eta t2  in
                    (uu____21369, uu____21376)  in
                  (match uu____21352 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3023_21418 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3023_21418.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3023_21418.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3023_21418.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3023_21418.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3023_21418.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3023_21418.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3023_21418.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3023_21418.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21439 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21439
                       then
                         let uu____21442 = destruct_flex_t not_abs wl  in
                         (match uu____21442 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3040_21459 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3040_21459.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3040_21459.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3040_21459.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3040_21459.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3040_21459.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3040_21459.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3040_21459.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3040_21459.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21462 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21462 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21485 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21485
                       then
                         let uu____21488 = destruct_flex_t not_abs wl  in
                         (match uu____21488 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3040_21505 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3040_21505.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3040_21505.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3040_21505.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3040_21505.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3040_21505.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3040_21505.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3040_21505.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3040_21505.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21508 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21508 orig))
                   | uu____21511 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21529,FStar_Syntax_Syntax.Tm_abs uu____21530) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21561 -> true
                    | uu____21581 -> false  in
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
                      (let uu____21641 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3002_21649 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3002_21649.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3002_21649.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3002_21649.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3002_21649.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3002_21649.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3002_21649.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3002_21649.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3002_21649.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3002_21649.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3002_21649.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3002_21649.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3002_21649.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3002_21649.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3002_21649.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3002_21649.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3002_21649.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3002_21649.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3002_21649.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3002_21649.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3002_21649.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3002_21649.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3002_21649.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3002_21649.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3002_21649.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3002_21649.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3002_21649.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3002_21649.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3002_21649.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3002_21649.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3002_21649.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3002_21649.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3002_21649.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3002_21649.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3002_21649.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3002_21649.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3002_21649.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3002_21649.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3002_21649.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3002_21649.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3002_21649.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3002_21649.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3002_21649.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21641 with
                       | (uu____21654,ty,uu____21656) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21665 =
                                 let uu____21666 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21666.FStar_Syntax_Syntax.n  in
                               match uu____21665 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21669 ->
                                   let uu____21676 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21676
                               | uu____21677 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21680 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21680
                             then
                               let uu____21685 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21687 =
                                 let uu____21689 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21689
                                  in
                               let uu____21690 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21685 uu____21687 uu____21690
                             else ());
                            r1))
                     in
                  let uu____21695 =
                    let uu____21712 = maybe_eta t1  in
                    let uu____21719 = maybe_eta t2  in
                    (uu____21712, uu____21719)  in
                  (match uu____21695 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3023_21761 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3023_21761.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3023_21761.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3023_21761.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3023_21761.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3023_21761.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3023_21761.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3023_21761.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3023_21761.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21782 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21782
                       then
                         let uu____21785 = destruct_flex_t not_abs wl  in
                         (match uu____21785 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3040_21802 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3040_21802.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3040_21802.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3040_21802.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3040_21802.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3040_21802.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3040_21802.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3040_21802.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3040_21802.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21805 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21805 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21828 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21828
                       then
                         let uu____21831 = destruct_flex_t not_abs wl  in
                         (match uu____21831 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3040_21848 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3040_21848.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3040_21848.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3040_21848.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3040_21848.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3040_21848.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3040_21848.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3040_21848.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3040_21848.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21851 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21851 orig))
                   | uu____21854 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21884 =
                    let uu____21889 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21889 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3063_21917 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3063_21917.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3063_21917.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3065_21919 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3065_21919.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3065_21919.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21920,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3063_21935 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3063_21935.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3063_21935.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3065_21937 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3065_21937.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3065_21937.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21938 -> (x1, x2)  in
                  (match uu____21884 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21957 = as_refinement false env t11  in
                       (match uu____21957 with
                        | (x12,phi11) ->
                            let uu____21965 = as_refinement false env t21  in
                            (match uu____21965 with
                             | (x22,phi21) ->
                                 ((let uu____21974 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21974
                                   then
                                     ((let uu____21979 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21981 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21983 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21979
                                         uu____21981 uu____21983);
                                      (let uu____21986 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21988 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21990 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21986
                                         uu____21988 uu____21990))
                                   else ());
                                  (let uu____21995 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21995 with
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
                                         let uu____22066 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22066
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22078 =
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
                                         (let uu____22091 =
                                            let uu____22094 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22094
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22091
                                            (p_guard base_prob));
                                         (let uu____22113 =
                                            let uu____22116 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22116
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22113
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22135 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22135)
                                          in
                                       let has_uvars =
                                         (let uu____22140 =
                                            let uu____22142 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22142
                                             in
                                          Prims.op_Negation uu____22140) ||
                                           (let uu____22146 =
                                              let uu____22148 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22148
                                               in
                                            Prims.op_Negation uu____22146)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22152 =
                                           let uu____22157 =
                                             let uu____22166 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22166]  in
                                           mk_t_problem wl1 uu____22157 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22152 with
                                          | (ref_prob,wl2) ->
                                              let uu____22188 =
                                                solve env1
                                                  (let uu___3107_22190 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3107_22190.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3107_22190.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3107_22190.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3107_22190.tcenv);
                                                     wl_implicits =
                                                       (uu___3107_22190.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22188 with
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
                                               | Success uu____22204 ->
                                                   let guard =
                                                     let uu____22212 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____22212
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3118_22221 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3118_22221.attempting);
                                                       wl_deferred =
                                                         (uu___3118_22221.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3118_22221.defer_ok);
                                                       smt_ok =
                                                         (uu___3118_22221.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3118_22221.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3118_22221.tcenv);
                                                       wl_implicits =
                                                         (uu___3118_22221.wl_implicits)
                                                     }  in
                                                   let uu____22223 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____22223))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22226,FStar_Syntax_Syntax.Tm_uvar uu____22227) ->
                  let uu____22252 = destruct_flex_t t1 wl  in
                  (match uu____22252 with
                   | (f1,wl1) ->
                       let uu____22259 = destruct_flex_t t2 wl1  in
                       (match uu____22259 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22266;
                    FStar_Syntax_Syntax.pos = uu____22267;
                    FStar_Syntax_Syntax.vars = uu____22268;_},uu____22269),FStar_Syntax_Syntax.Tm_uvar
                 uu____22270) ->
                  let uu____22319 = destruct_flex_t t1 wl  in
                  (match uu____22319 with
                   | (f1,wl1) ->
                       let uu____22326 = destruct_flex_t t2 wl1  in
                       (match uu____22326 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22333,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22334;
                    FStar_Syntax_Syntax.pos = uu____22335;
                    FStar_Syntax_Syntax.vars = uu____22336;_},uu____22337))
                  ->
                  let uu____22386 = destruct_flex_t t1 wl  in
                  (match uu____22386 with
                   | (f1,wl1) ->
                       let uu____22393 = destruct_flex_t t2 wl1  in
                       (match uu____22393 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22400;
                    FStar_Syntax_Syntax.pos = uu____22401;
                    FStar_Syntax_Syntax.vars = uu____22402;_},uu____22403),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22404;
                    FStar_Syntax_Syntax.pos = uu____22405;
                    FStar_Syntax_Syntax.vars = uu____22406;_},uu____22407))
                  ->
                  let uu____22480 = destruct_flex_t t1 wl  in
                  (match uu____22480 with
                   | (f1,wl1) ->
                       let uu____22487 = destruct_flex_t t2 wl1  in
                       (match uu____22487 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22494,uu____22495) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22508 = destruct_flex_t t1 wl  in
                  (match uu____22508 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22515;
                    FStar_Syntax_Syntax.pos = uu____22516;
                    FStar_Syntax_Syntax.vars = uu____22517;_},uu____22518),uu____22519)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22556 = destruct_flex_t t1 wl  in
                  (match uu____22556 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22563,FStar_Syntax_Syntax.Tm_uvar uu____22564) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22577,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22578;
                    FStar_Syntax_Syntax.pos = uu____22579;
                    FStar_Syntax_Syntax.vars = uu____22580;_},uu____22581))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22618,FStar_Syntax_Syntax.Tm_arrow uu____22619) ->
                  solve_t' env
                    (let uu___3218_22647 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3218_22647.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3218_22647.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3218_22647.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3218_22647.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3218_22647.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3218_22647.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3218_22647.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3218_22647.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3218_22647.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22648;
                    FStar_Syntax_Syntax.pos = uu____22649;
                    FStar_Syntax_Syntax.vars = uu____22650;_},uu____22651),FStar_Syntax_Syntax.Tm_arrow
                 uu____22652) ->
                  solve_t' env
                    (let uu___3218_22704 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3218_22704.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3218_22704.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3218_22704.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3218_22704.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3218_22704.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3218_22704.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3218_22704.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3218_22704.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3218_22704.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22705,FStar_Syntax_Syntax.Tm_uvar uu____22706) ->
                  let uu____22719 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22719
              | (uu____22720,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22721;
                    FStar_Syntax_Syntax.pos = uu____22722;
                    FStar_Syntax_Syntax.vars = uu____22723;_},uu____22724))
                  ->
                  let uu____22761 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22761
              | (FStar_Syntax_Syntax.Tm_uvar uu____22762,uu____22763) ->
                  let uu____22776 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22776
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22777;
                    FStar_Syntax_Syntax.pos = uu____22778;
                    FStar_Syntax_Syntax.vars = uu____22779;_},uu____22780),uu____22781)
                  ->
                  let uu____22818 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22818
              | (FStar_Syntax_Syntax.Tm_refine uu____22819,uu____22820) ->
                  let t21 =
                    let uu____22828 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22828  in
                  solve_t env
                    (let uu___3253_22854 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3253_22854.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3253_22854.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3253_22854.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3253_22854.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3253_22854.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3253_22854.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3253_22854.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3253_22854.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3253_22854.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22855,FStar_Syntax_Syntax.Tm_refine uu____22856) ->
                  let t11 =
                    let uu____22864 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22864  in
                  solve_t env
                    (let uu___3260_22890 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3260_22890.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3260_22890.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3260_22890.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3260_22890.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3260_22890.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3260_22890.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3260_22890.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3260_22890.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3260_22890.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22972 =
                    let uu____22973 = guard_of_prob env wl problem t1 t2  in
                    match uu____22973 with
                    | (guard,wl1) ->
                        let uu____22980 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22980
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23199 = br1  in
                        (match uu____23199 with
                         | (p1,w1,uu____23228) ->
                             let uu____23245 = br2  in
                             (match uu____23245 with
                              | (p2,w2,uu____23268) ->
                                  let uu____23273 =
                                    let uu____23275 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23275  in
                                  if uu____23273
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23302 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23302 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23339 = br2  in
                                         (match uu____23339 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23372 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23372
                                                 in
                                              let uu____23377 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23408,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23429) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23488 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23488 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23377
                                                (fun uu____23560  ->
                                                   match uu____23560 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23597 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23597
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23618
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23618
                                                              then
                                                                let uu____23623
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23625
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23623
                                                                  uu____23625
                                                              else ());
                                                             (let uu____23631
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23631
                                                                (fun
                                                                   uu____23667
                                                                    ->
                                                                   match uu____23667
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
                    | uu____23796 -> FStar_Pervasives_Native.None  in
                  let uu____23837 = solve_branches wl brs1 brs2  in
                  (match uu____23837 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23863 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23863 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23890 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23890 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23924 =
                                FStar_List.map
                                  (fun uu____23936  ->
                                     match uu____23936 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23924  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23945 =
                              let uu____23946 =
                                let uu____23947 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23947
                                  (let uu___3359_23955 = wl3  in
                                   {
                                     attempting =
                                       (uu___3359_23955.attempting);
                                     wl_deferred =
                                       (uu___3359_23955.wl_deferred);
                                     ctr = (uu___3359_23955.ctr);
                                     defer_ok = (uu___3359_23955.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3359_23955.umax_heuristic_ok);
                                     tcenv = (uu___3359_23955.tcenv);
                                     wl_implicits =
                                       (uu___3359_23955.wl_implicits)
                                   })
                                 in
                              solve env uu____23946  in
                            (match uu____23945 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23960 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____23966,uu____23967) ->
                  let head1 =
                    let uu____23991 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23991
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24037 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24037
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24083 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24083
                    then
                      let uu____24087 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24089 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24091 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24087 uu____24089 uu____24091
                    else ());
                   (let no_free_uvars t =
                      (let uu____24105 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24105) &&
                        (let uu____24109 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24109)
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
                      let uu____24128 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24128 = FStar_Syntax_Util.Equal  in
                    let uu____24129 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24129
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24133 = equal t1 t2  in
                         (if uu____24133
                          then
                            let uu____24136 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24136
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24141 =
                            let uu____24148 = equal t1 t2  in
                            if uu____24148
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24161 = mk_eq2 wl env orig t1 t2  in
                               match uu____24161 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24141 with
                          | (guard,wl1) ->
                              let uu____24182 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24182))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24185,uu____24186) ->
                  let head1 =
                    let uu____24194 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24194
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24240 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24240
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24286 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24286
                    then
                      let uu____24290 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24292 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24294 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24290 uu____24292 uu____24294
                    else ());
                   (let no_free_uvars t =
                      (let uu____24308 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24308) &&
                        (let uu____24312 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24312)
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
                      let uu____24331 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24331 = FStar_Syntax_Util.Equal  in
                    let uu____24332 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24332
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24336 = equal t1 t2  in
                         (if uu____24336
                          then
                            let uu____24339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24344 =
                            let uu____24351 = equal t1 t2  in
                            if uu____24351
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24364 = mk_eq2 wl env orig t1 t2  in
                               match uu____24364 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24344 with
                          | (guard,wl1) ->
                              let uu____24385 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24385))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24388,uu____24389) ->
                  let head1 =
                    let uu____24391 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24391
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24437 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24437
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24483 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24483
                    then
                      let uu____24487 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24489 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24491 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24487 uu____24489 uu____24491
                    else ());
                   (let no_free_uvars t =
                      (let uu____24505 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24505) &&
                        (let uu____24509 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24509)
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
                      let uu____24528 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24528 = FStar_Syntax_Util.Equal  in
                    let uu____24529 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24529
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24533 = equal t1 t2  in
                         (if uu____24533
                          then
                            let uu____24536 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24536
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24541 =
                            let uu____24548 = equal t1 t2  in
                            if uu____24548
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24561 = mk_eq2 wl env orig t1 t2  in
                               match uu____24561 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24541 with
                          | (guard,wl1) ->
                              let uu____24582 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24582))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24585,uu____24586) ->
                  let head1 =
                    let uu____24588 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24588
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24634 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24634
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24680 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24680
                    then
                      let uu____24684 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24686 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24688 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24684 uu____24686 uu____24688
                    else ());
                   (let no_free_uvars t =
                      (let uu____24702 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24702) &&
                        (let uu____24706 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24706)
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
                      let uu____24725 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24725 = FStar_Syntax_Util.Equal  in
                    let uu____24726 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24726
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24730 = equal t1 t2  in
                         (if uu____24730
                          then
                            let uu____24733 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24733
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24738 =
                            let uu____24745 = equal t1 t2  in
                            if uu____24745
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24758 = mk_eq2 wl env orig t1 t2  in
                               match uu____24758 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24738 with
                          | (guard,wl1) ->
                              let uu____24779 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24779))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24782,uu____24783) ->
                  let head1 =
                    let uu____24785 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24785
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24825 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24825
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24865 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24865
                    then
                      let uu____24869 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24871 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24873 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24869 uu____24871 uu____24873
                    else ());
                   (let no_free_uvars t =
                      (let uu____24887 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24887) &&
                        (let uu____24891 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24891)
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
                      let uu____24910 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24910 = FStar_Syntax_Util.Equal  in
                    let uu____24911 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24911
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24915 = equal t1 t2  in
                         (if uu____24915
                          then
                            let uu____24918 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24918
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24923 =
                            let uu____24930 = equal t1 t2  in
                            if uu____24930
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24943 = mk_eq2 wl env orig t1 t2  in
                               match uu____24943 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24923 with
                          | (guard,wl1) ->
                              let uu____24964 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24964))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24967,uu____24968) ->
                  let head1 =
                    let uu____24986 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24986
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25026 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25026
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25066 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25066
                    then
                      let uu____25070 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25072 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25074 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25070 uu____25072 uu____25074
                    else ());
                   (let no_free_uvars t =
                      (let uu____25088 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25088) &&
                        (let uu____25092 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25092)
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
                      let uu____25111 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25111 = FStar_Syntax_Util.Equal  in
                    let uu____25112 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25112
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25116 = equal t1 t2  in
                         (if uu____25116
                          then
                            let uu____25119 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25119
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25124 =
                            let uu____25131 = equal t1 t2  in
                            if uu____25131
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25144 = mk_eq2 wl env orig t1 t2  in
                               match uu____25144 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25124 with
                          | (guard,wl1) ->
                              let uu____25165 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25165))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25168,FStar_Syntax_Syntax.Tm_match uu____25169) ->
                  let head1 =
                    let uu____25193 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25193
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25233 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25233
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25273 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25273
                    then
                      let uu____25277 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25279 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25281 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25277 uu____25279 uu____25281
                    else ());
                   (let no_free_uvars t =
                      (let uu____25295 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25295) &&
                        (let uu____25299 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25299)
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
                      let uu____25318 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25318 = FStar_Syntax_Util.Equal  in
                    let uu____25319 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25319
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25323 = equal t1 t2  in
                         (if uu____25323
                          then
                            let uu____25326 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25326
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25331 =
                            let uu____25338 = equal t1 t2  in
                            if uu____25338
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25351 = mk_eq2 wl env orig t1 t2  in
                               match uu____25351 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25331 with
                          | (guard,wl1) ->
                              let uu____25372 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25372))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25375,FStar_Syntax_Syntax.Tm_uinst uu____25376) ->
                  let head1 =
                    let uu____25384 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25384
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25424 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25424
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25464 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25464
                    then
                      let uu____25468 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25470 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25472 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25468 uu____25470 uu____25472
                    else ());
                   (let no_free_uvars t =
                      (let uu____25486 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25486) &&
                        (let uu____25490 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25490)
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
                      let uu____25509 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25509 = FStar_Syntax_Util.Equal  in
                    let uu____25510 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25510
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25514 = equal t1 t2  in
                         (if uu____25514
                          then
                            let uu____25517 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25517
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25522 =
                            let uu____25529 = equal t1 t2  in
                            if uu____25529
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25542 = mk_eq2 wl env orig t1 t2  in
                               match uu____25542 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25522 with
                          | (guard,wl1) ->
                              let uu____25563 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25563))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25566,FStar_Syntax_Syntax.Tm_name uu____25567) ->
                  let head1 =
                    let uu____25569 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25569
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25609 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25609
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25649 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25649
                    then
                      let uu____25653 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25655 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25657 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25653 uu____25655 uu____25657
                    else ());
                   (let no_free_uvars t =
                      (let uu____25671 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25671) &&
                        (let uu____25675 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25675)
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
                      let uu____25694 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25694 = FStar_Syntax_Util.Equal  in
                    let uu____25695 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25695
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25699 = equal t1 t2  in
                         (if uu____25699
                          then
                            let uu____25702 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25702
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25707 =
                            let uu____25714 = equal t1 t2  in
                            if uu____25714
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25727 = mk_eq2 wl env orig t1 t2  in
                               match uu____25727 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25707 with
                          | (guard,wl1) ->
                              let uu____25748 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25748))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25751,FStar_Syntax_Syntax.Tm_constant uu____25752) ->
                  let head1 =
                    let uu____25754 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25754
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25794 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25794
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25834 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25834
                    then
                      let uu____25838 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25840 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25842 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25838 uu____25840 uu____25842
                    else ());
                   (let no_free_uvars t =
                      (let uu____25856 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25856) &&
                        (let uu____25860 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25860)
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
                      let uu____25879 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25879 = FStar_Syntax_Util.Equal  in
                    let uu____25880 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25880
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25884 = equal t1 t2  in
                         (if uu____25884
                          then
                            let uu____25887 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25887
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25892 =
                            let uu____25899 = equal t1 t2  in
                            if uu____25899
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25912 = mk_eq2 wl env orig t1 t2  in
                               match uu____25912 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25892 with
                          | (guard,wl1) ->
                              let uu____25933 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25933))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25936,FStar_Syntax_Syntax.Tm_fvar uu____25937) ->
                  let head1 =
                    let uu____25939 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25939
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25985 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25985
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26031 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26031
                    then
                      let uu____26035 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26037 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26039 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26035 uu____26037 uu____26039
                    else ());
                   (let no_free_uvars t =
                      (let uu____26053 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26053) &&
                        (let uu____26057 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26057)
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
                      let uu____26076 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26076 = FStar_Syntax_Util.Equal  in
                    let uu____26077 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26077
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26081 = equal t1 t2  in
                         (if uu____26081
                          then
                            let uu____26084 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26084
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26089 =
                            let uu____26096 = equal t1 t2  in
                            if uu____26096
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26109 = mk_eq2 wl env orig t1 t2  in
                               match uu____26109 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26089 with
                          | (guard,wl1) ->
                              let uu____26130 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26130))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26133,FStar_Syntax_Syntax.Tm_app uu____26134) ->
                  let head1 =
                    let uu____26152 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26152
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26192 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26192
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26232 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26232
                    then
                      let uu____26236 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26238 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26240 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26236 uu____26238 uu____26240
                    else ());
                   (let no_free_uvars t =
                      (let uu____26254 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26254) &&
                        (let uu____26258 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26258)
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
                      let uu____26277 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26277 = FStar_Syntax_Util.Equal  in
                    let uu____26278 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26278
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26282 = equal t1 t2  in
                         (if uu____26282
                          then
                            let uu____26285 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26285
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26290 =
                            let uu____26297 = equal t1 t2  in
                            if uu____26297
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26310 = mk_eq2 wl env orig t1 t2  in
                               match uu____26310 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26290 with
                          | (guard,wl1) ->
                              let uu____26331 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26331))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26334,FStar_Syntax_Syntax.Tm_let uu____26335) ->
                  let uu____26362 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26362
                  then
                    let uu____26365 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26365
                  else
                    (let uu____26368 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26368 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26371,uu____26372) ->
                  let uu____26386 =
                    let uu____26392 =
                      let uu____26394 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26396 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26398 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26400 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26394 uu____26396 uu____26398 uu____26400
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26392)
                     in
                  FStar_Errors.raise_error uu____26386
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26404,FStar_Syntax_Syntax.Tm_let uu____26405) ->
                  let uu____26419 =
                    let uu____26425 =
                      let uu____26427 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26429 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26431 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26433 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26427 uu____26429 uu____26431 uu____26433
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26425)
                     in
                  FStar_Errors.raise_error uu____26419
                    t1.FStar_Syntax_Syntax.pos
              | uu____26437 ->
                  let uu____26442 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26442 orig))))

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
          (let uu____26508 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26508
           then
             let uu____26513 =
               let uu____26515 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26515  in
             let uu____26516 =
               let uu____26518 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26518  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26513 uu____26516
           else ());
          (let uu____26522 =
             let uu____26524 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26524  in
           if uu____26522
           then
             let uu____26527 =
               FStar_Thunk.mk
                 (fun uu____26532  ->
                    let uu____26533 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26535 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26533 uu____26535)
                in
             giveup env uu____26527 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26557 =
                  FStar_Thunk.mk
                    (fun uu____26562  ->
                       let uu____26563 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26565 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26563 uu____26565)
                   in
                giveup env uu____26557 orig)
             else
               (let uu____26570 =
                  sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                match uu____26570 with
                | (ret_sub_prob,wl1) ->
                    let uu____26578 =
                      FStar_List.fold_right2
                        (fun uu____26615  ->
                           fun uu____26616  ->
                             fun uu____26617  ->
                               match (uu____26615, uu____26616, uu____26617)
                               with
                               | ((a1,uu____26661),(a2,uu____26663),(arg_sub_probs,wl2))
                                   ->
                                   let uu____26696 =
                                     sub_prob wl2 a1
                                       FStar_TypeChecker_Common.EQ a2
                                       "effect arg"
                                      in
                                   (match uu____26696 with
                                    | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                        c1_comp.FStar_Syntax_Syntax.effect_args
                        c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                       in
                    (match uu____26578 with
                     | (arg_sub_probs,wl2) ->
                         let sub_probs =
                           let uu____26723 =
                             let uu____26726 =
                               FStar_All.pipe_right
                                 g_lift.FStar_TypeChecker_Common.deferred
                                 (FStar_List.map FStar_Pervasives_Native.snd)
                                in
                             FStar_List.append arg_sub_probs uu____26726  in
                           ret_sub_prob :: uu____26723  in
                         let guard =
                           let guard =
                             let uu____26748 =
                               FStar_List.map p_guard sub_probs  in
                             FStar_Syntax_Util.mk_conj_l uu____26748  in
                           match g_lift.FStar_TypeChecker_Common.guard_f with
                           | FStar_TypeChecker_Common.Trivial  -> guard
                           | FStar_TypeChecker_Common.NonTrivial f ->
                               FStar_Syntax_Util.mk_conj guard f
                            in
                         let wl3 =
                           let uu___3499_26757 = wl2  in
                           {
                             attempting = (uu___3499_26757.attempting);
                             wl_deferred = (uu___3499_26757.wl_deferred);
                             ctr = (uu___3499_26757.ctr);
                             defer_ok = (uu___3499_26757.defer_ok);
                             smt_ok = (uu___3499_26757.smt_ok);
                             umax_heuristic_ok =
                               (uu___3499_26757.umax_heuristic_ok);
                             tcenv = (uu___3499_26757.tcenv);
                             wl_implicits =
                               (FStar_List.append
                                  g_lift.FStar_TypeChecker_Common.implicits
                                  wl2.wl_implicits)
                           }  in
                         let wl4 =
                           solve_prob orig
                             (FStar_Pervasives_Native.Some guard) [] wl3
                            in
                         let uu____26759 = attempt sub_probs wl4  in
                         solve env uu____26759)))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26777 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26777
           then
             let uu____26782 =
               let uu____26784 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26784
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26786 =
               let uu____26788 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26788
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26782 uu____26786
           else ());
          (let uu____26793 =
             let uu____26798 =
               let uu____26803 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26803
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26798
               (fun uu____26820  ->
                  match uu____26820 with
                  | (c,g) ->
                      let uu____26831 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26831, g))
              in
           match uu____26793 with
           | (c12,g_lift) ->
               ((let uu____26835 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26835
                 then
                   let uu____26840 =
                     let uu____26842 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26842
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26844 =
                     let uu____26846 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26846
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26840 uu____26844
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3519_26856 = wl  in
                     {
                       attempting = (uu___3519_26856.attempting);
                       wl_deferred = (uu___3519_26856.wl_deferred);
                       ctr = (uu___3519_26856.ctr);
                       defer_ok = (uu___3519_26856.defer_ok);
                       smt_ok = (uu___3519_26856.smt_ok);
                       umax_heuristic_ok =
                         (uu___3519_26856.umax_heuristic_ok);
                       tcenv = (uu___3519_26856.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26857 =
                     let rec is_uvar1 t =
                       let uu____26871 =
                         let uu____26872 = FStar_Syntax_Subst.compress t  in
                         uu____26872.FStar_Syntax_Syntax.n  in
                       match uu____26871 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26876 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26891) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26897) ->
                           is_uvar1 t1
                       | uu____26922 -> false  in
                     FStar_List.fold_right2
                       (fun uu____26956  ->
                          fun uu____26957  ->
                            fun uu____26958  ->
                              match (uu____26956, uu____26957, uu____26958)
                              with
                              | ((a1,uu____27002),(a2,uu____27004),(is_sub_probs,wl2))
                                  ->
                                  let uu____27037 = is_uvar1 a1  in
                                  if uu____27037
                                  then
                                    ((let uu____27047 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27047
                                      then
                                        let uu____27052 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27054 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27052 uu____27054
                                      else ());
                                     (let uu____27059 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27059 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26857 with
                   | (is_sub_probs,wl2) ->
                       let uu____27087 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27087 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27095 =
                              let uu____27100 =
                                let uu____27101 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27101
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27100
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27095 with
                             | (uu____27108,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27119 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27121 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27119 s uu____27121
                                    in
                                 let uu____27124 =
                                   let uu____27153 =
                                     let uu____27154 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27154.FStar_Syntax_Syntax.n  in
                                   match uu____27153 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27214 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27214 with
                                        | (a::bs1,c3) ->
                                            let uu____27270 =
                                              let uu____27289 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27289
                                                (fun uu____27393  ->
                                                   match uu____27393 with
                                                   | (l1,l2) ->
                                                       let uu____27466 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27466))
                                               in
                                            (match uu____27270 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27571 ->
                                       let uu____27572 =
                                         let uu____27578 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27578)
                                          in
                                       FStar_Errors.raise_error uu____27572 r
                                    in
                                 (match uu____27124 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27654 =
                                        let uu____27661 =
                                          let uu____27662 =
                                            let uu____27663 =
                                              let uu____27670 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27670,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27663
                                             in
                                          [uu____27662]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27661
                                          (fun b  ->
                                             let uu____27686 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27688 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27690 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27686 uu____27688
                                               uu____27690) r
                                         in
                                      (match uu____27654 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           let wl4 =
                                             let uu___3587_27700 = wl3  in
                                             {
                                               attempting =
                                                 (uu___3587_27700.attempting);
                                               wl_deferred =
                                                 (uu___3587_27700.wl_deferred);
                                               ctr = (uu___3587_27700.ctr);
                                               defer_ok =
                                                 (uu___3587_27700.defer_ok);
                                               smt_ok =
                                                 (uu___3587_27700.smt_ok);
                                               umax_heuristic_ok =
                                                 (uu___3587_27700.umax_heuristic_ok);
                                               tcenv =
                                                 (uu___3587_27700.tcenv);
                                               wl_implicits =
                                                 (FStar_List.append
                                                    g_uvars.FStar_TypeChecker_Common.implicits
                                                    wl3.wl_implicits)
                                             }  in
                                           let substs =
                                             FStar_List.map2
                                               (fun b  ->
                                                  fun t  ->
                                                    let uu____27725 =
                                                      let uu____27732 =
                                                        FStar_All.pipe_right
                                                          b
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      (uu____27732, t)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____27725) (a_b ::
                                               rest_bs)
                                               ((c21.FStar_Syntax_Syntax.result_typ)
                                               :: rest_bs_uvars)
                                              in
                                           let uu____27749 =
                                             let f_sort_is =
                                               let uu____27759 =
                                                 let uu____27760 =
                                                   let uu____27763 =
                                                     let uu____27764 =
                                                       FStar_All.pipe_right
                                                         f_b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     uu____27764.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Subst.compress
                                                     uu____27763
                                                    in
                                                 uu____27760.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____27759 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____27775,uu____27776::is)
                                                   ->
                                                   let uu____27818 =
                                                     FStar_All.pipe_right is
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____27818
                                                     (FStar_List.map
                                                        (FStar_Syntax_Subst.subst
                                                           substs))
                                               | uu____27851 ->
                                                   let uu____27852 =
                                                     let uu____27858 =
                                                       stronger_t_shape_error
                                                         "type of f is not a repr type"
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                       uu____27858)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____27852 r
                                                in
                                             let uu____27864 =
                                               FStar_All.pipe_right
                                                 c12.FStar_Syntax_Syntax.effect_args
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             FStar_List.fold_left2
                                               (fun uu____27899  ->
                                                  fun f_sort_i  ->
                                                    fun c1_i  ->
                                                      match uu____27899 with
                                                      | (ps,wl5) ->
                                                          let uu____27920 =
                                                            sub_prob wl5
                                                              f_sort_i
                                                              FStar_TypeChecker_Common.EQ
                                                              c1_i
                                                              "indices of c1"
                                                             in
                                                          (match uu____27920
                                                           with
                                                           | (p,wl6) ->
                                                               ((FStar_List.append
                                                                   ps 
                                                                   [p]), wl6)))
                                               ([], wl4) f_sort_is
                                               uu____27864
                                              in
                                           (match uu____27749 with
                                            | (f_sub_probs,wl5) ->
                                                let stronger_ct =
                                                  let uu____27945 =
                                                    FStar_All.pipe_right
                                                      stronger_c
                                                      (FStar_Syntax_Subst.subst_comp
                                                         substs)
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____27945
                                                    FStar_Syntax_Util.comp_to_comp_typ
                                                   in
                                                let uu____27946 =
                                                  let g_sort_is =
                                                    let uu____27956 =
                                                      let uu____27957 =
                                                        FStar_Syntax_Subst.compress
                                                          stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         in
                                                      uu____27957.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____27956 with
                                                    | FStar_Syntax_Syntax.Tm_app
                                                        (uu____27962,uu____27963::is)
                                                        ->
                                                        FStar_All.pipe_right
                                                          is
                                                          (FStar_List.map
                                                             FStar_Pervasives_Native.fst)
                                                    | uu____28031 ->
                                                        let uu____28032 =
                                                          let uu____28038 =
                                                            stronger_t_shape_error
                                                              "return type is not a repr type"
                                                             in
                                                          (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                            uu____28038)
                                                           in
                                                        FStar_Errors.raise_error
                                                          uu____28032 r
                                                     in
                                                  let uu____28044 =
                                                    FStar_All.pipe_right
                                                      c21.FStar_Syntax_Syntax.effect_args
                                                      (FStar_List.map
                                                         FStar_Pervasives_Native.fst)
                                                     in
                                                  FStar_List.fold_left2
                                                    (fun uu____28079  ->
                                                       fun g_sort_i  ->
                                                         fun c2_i  ->
                                                           match uu____28079
                                                           with
                                                           | (ps,wl6) ->
                                                               let uu____28100
                                                                 =
                                                                 sub_prob wl6
                                                                   g_sort_i
                                                                   FStar_TypeChecker_Common.EQ
                                                                   c2_i
                                                                   "indices of c2"
                                                                  in
                                                               (match uu____28100
                                                                with
                                                                | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                    ([], wl5) g_sort_is
                                                    uu____28044
                                                   in
                                                (match uu____27946 with
                                                 | (g_sub_probs,wl6) ->
                                                     let fml =
                                                       let uu____28127 =
                                                         let uu____28132 =
                                                           FStar_List.hd
                                                             stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                            in
                                                         let uu____28133 =
                                                           let uu____28134 =
                                                             FStar_List.hd
                                                               stronger_ct.FStar_Syntax_Syntax.effect_args
                                                              in
                                                           FStar_Pervasives_Native.fst
                                                             uu____28134
                                                            in
                                                         (uu____28132,
                                                           uu____28133)
                                                          in
                                                       match uu____28127 with
                                                       | (u,wp) ->
                                                           let trivial_post =
                                                             let ts =
                                                               let uu____28161
                                                                 =
                                                                 FStar_TypeChecker_Env.lookup_definition
                                                                   [FStar_TypeChecker_Env.NoDelta]
                                                                   env
                                                                   FStar_Parser_Const.trivial_pure_post_lid
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____28161
                                                                 FStar_Util.must
                                                                in
                                                             let uu____28178
                                                               =
                                                               FStar_TypeChecker_Env.inst_tscheme_with
                                                                 ts [u]
                                                                in
                                                             match uu____28178
                                                             with
                                                             | (uu____28183,t)
                                                                 ->
                                                                 let uu____28185
                                                                   =
                                                                   let uu____28190
                                                                    =
                                                                    let uu____28191
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    stronger_ct.FStar_Syntax_Syntax.result_typ
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____28191]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    t
                                                                    uu____28190
                                                                    in
                                                                 uu____28185
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Range.dummyRange
                                                              in
                                                           let uu____28224 =
                                                             let uu____28229
                                                               =
                                                               let uu____28230
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   trivial_post
                                                                   FStar_Syntax_Syntax.as_arg
                                                                  in
                                                               [uu____28230]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               wp uu____28229
                                                              in
                                                           uu____28224
                                                             FStar_Pervasives_Native.None
                                                             FStar_Range.dummyRange
                                                        in
                                                     let sub_probs =
                                                       let uu____28266 =
                                                         let uu____28269 =
                                                           let uu____28272 =
                                                             let uu____28275
                                                               =
                                                               FStar_All.pipe_right
                                                                 g_lift.FStar_TypeChecker_Common.deferred
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             FStar_List.append
                                                               g_sub_probs
                                                               uu____28275
                                                              in
                                                           FStar_List.append
                                                             f_sub_probs
                                                             uu____28272
                                                            in
                                                         FStar_List.append
                                                           is_sub_probs
                                                           uu____28269
                                                          in
                                                       ret_sub_prob ::
                                                         uu____28266
                                                        in
                                                     let guard =
                                                       let guard =
                                                         let uu____28299 =
                                                           FStar_List.map
                                                             p_guard
                                                             sub_probs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____28299
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
                                                       let uu____28310 =
                                                         let uu____28313 =
                                                           FStar_Syntax_Util.mk_conj
                                                             guard fml
                                                            in
                                                         FStar_All.pipe_left
                                                           (fun _28316  ->
                                                              FStar_Pervasives_Native.Some
                                                                _28316)
                                                           uu____28313
                                                          in
                                                       solve_prob orig
                                                         uu____28310 [] wl6
                                                        in
                                                     let uu____28317 =
                                                       attempt sub_probs wl7
                                                        in
                                                     solve env uu____28317)))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28340 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28342 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28342]
              | x -> x  in
            let c12 =
              let uu___3658_28345 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3658_28345.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3658_28345.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3658_28345.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3658_28345.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28346 =
              let uu____28351 =
                FStar_All.pipe_right
                  (let uu___3661_28353 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3661_28353.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3661_28353.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3661_28353.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3661_28353.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28351
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28346
              (fun uu____28367  ->
                 match uu____28367 with
                 | (c,g) ->
                     let uu____28374 =
                       let uu____28376 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28376  in
                     if uu____28374
                     then
                       let uu____28379 =
                         let uu____28385 =
                           let uu____28387 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28389 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28387 uu____28389
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28385)
                          in
                       FStar_Errors.raise_error uu____28379 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28395 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28395
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28401 = lift_c1 ()  in
               solve_eq uu____28401 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28410  ->
                         match uu___31_28410 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28415 -> false))
                  in
               let uu____28417 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28447)::uu____28448,(wp2,uu____28450)::uu____28451)
                     -> (wp1, wp2)
                 | uu____28524 ->
                     let uu____28549 =
                       let uu____28555 =
                         let uu____28557 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28559 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28557 uu____28559
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28555)
                        in
                     FStar_Errors.raise_error uu____28549
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28417 with
               | (wpc1,wpc2) ->
                   let uu____28569 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28569
                   then
                     let uu____28572 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28572 wl
                   else
                     (let uu____28576 =
                        let uu____28583 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28583  in
                      match uu____28576 with
                      | (c2_decl,qualifiers) ->
                          let uu____28604 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28604
                          then
                            let c1_repr =
                              let uu____28611 =
                                let uu____28612 =
                                  let uu____28613 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28613  in
                                let uu____28614 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28612 uu____28614
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28611
                               in
                            let c2_repr =
                              let uu____28617 =
                                let uu____28618 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28619 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28618 uu____28619
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28617
                               in
                            let uu____28621 =
                              let uu____28626 =
                                let uu____28628 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28630 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28628
                                  uu____28630
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28626
                               in
                            (match uu____28621 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28636 = attempt [prob] wl2  in
                                 solve env uu____28636)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28656 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28656
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28679 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28679
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
                                        let uu____28689 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28689 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28696 =
                                        let uu____28703 =
                                          let uu____28704 =
                                            let uu____28721 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28724 =
                                              let uu____28735 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28735; wpc1_2]  in
                                            (uu____28721, uu____28724)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28704
                                           in
                                        FStar_Syntax_Syntax.mk uu____28703
                                         in
                                      uu____28696
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
                                     let uu____28784 =
                                       let uu____28791 =
                                         let uu____28792 =
                                           let uu____28809 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28812 =
                                             let uu____28823 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28832 =
                                               let uu____28843 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28843; wpc1_2]  in
                                             uu____28823 :: uu____28832  in
                                           (uu____28809, uu____28812)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28792
                                          in
                                       FStar_Syntax_Syntax.mk uu____28791  in
                                     uu____28784 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28897 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28897
                              then
                                let uu____28902 =
                                  let uu____28904 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28904
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28902
                              else ());
                             (let uu____28908 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28908 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28917 =
                                      let uu____28920 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28923  ->
                                           FStar_Pervasives_Native.Some
                                             _28923) uu____28920
                                       in
                                    solve_prob orig uu____28917 [] wl1  in
                                  let uu____28924 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28924))))
           in
        let uu____28925 = FStar_Util.physical_equality c1 c2  in
        if uu____28925
        then
          let uu____28928 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28928
        else
          ((let uu____28932 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28932
            then
              let uu____28937 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28939 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28937
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28939
            else ());
           (let uu____28944 =
              let uu____28953 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28956 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28953, uu____28956)  in
            match uu____28944 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28974),FStar_Syntax_Syntax.Total
                    (t2,uu____28976)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____28993 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28993 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____28995,FStar_Syntax_Syntax.Total uu____28996) ->
                     let uu____29013 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29013 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29017),FStar_Syntax_Syntax.Total
                    (t2,uu____29019)) ->
                     let uu____29036 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29036 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29039),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29041)) ->
                     let uu____29058 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29058 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29061),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29063)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29080 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29080 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29083),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29085)) ->
                     let uu____29102 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29102 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29105,FStar_Syntax_Syntax.Comp uu____29106) ->
                     let uu____29115 =
                       let uu___3785_29118 = problem  in
                       let uu____29121 =
                         let uu____29122 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29122
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3785_29118.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29121;
                         FStar_TypeChecker_Common.relation =
                           (uu___3785_29118.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3785_29118.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3785_29118.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3785_29118.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3785_29118.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3785_29118.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3785_29118.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3785_29118.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29115 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29123,FStar_Syntax_Syntax.Comp uu____29124) ->
                     let uu____29133 =
                       let uu___3785_29136 = problem  in
                       let uu____29139 =
                         let uu____29140 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29140
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3785_29136.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29139;
                         FStar_TypeChecker_Common.relation =
                           (uu___3785_29136.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3785_29136.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3785_29136.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3785_29136.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3785_29136.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3785_29136.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3785_29136.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3785_29136.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29133 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29141,FStar_Syntax_Syntax.GTotal uu____29142) ->
                     let uu____29151 =
                       let uu___3797_29154 = problem  in
                       let uu____29157 =
                         let uu____29158 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29158
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29154.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3797_29154.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29154.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29157;
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29154.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29154.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29154.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29154.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29154.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29154.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29151 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29159,FStar_Syntax_Syntax.Total uu____29160) ->
                     let uu____29169 =
                       let uu___3797_29172 = problem  in
                       let uu____29175 =
                         let uu____29176 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29176
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29172.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3797_29172.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29172.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29175;
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29172.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29172.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29172.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29172.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29172.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29172.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29169 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29177,FStar_Syntax_Syntax.Comp uu____29178) ->
                     let uu____29179 =
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
                     if uu____29179
                     then
                       let uu____29182 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29182 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29189 =
                            let uu____29194 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29194
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29203 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29204 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29203, uu____29204))
                             in
                          match uu____29189 with
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
                           (let uu____29212 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29212
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29220 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29220 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29223 =
                                  FStar_Thunk.mk
                                    (fun uu____29228  ->
                                       let uu____29229 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29231 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29229 uu____29231)
                                   in
                                giveup env uu____29223 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29242 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29242 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29292 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29292 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29317 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29348  ->
                match uu____29348 with
                | (u1,u2) ->
                    let uu____29356 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29358 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29356 uu____29358))
         in
      FStar_All.pipe_right uu____29317 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29395,[])) when
          let uu____29422 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29422 -> "{}"
      | uu____29425 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29452 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29452
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29464 =
              FStar_List.map
                (fun uu____29477  ->
                   match uu____29477 with
                   | (uu____29484,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29464 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29495 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29495 imps
  
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
                  let uu____29552 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29552
                  then
                    let uu____29560 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29562 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29560
                      (rel_to_string rel) uu____29562
                  else "TOP"  in
                let uu____29568 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29568 with
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
              let uu____29628 =
                let uu____29631 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29634  -> FStar_Pervasives_Native.Some _29634)
                  uu____29631
                 in
              FStar_Syntax_Syntax.new_bv uu____29628 t1  in
            let uu____29635 =
              let uu____29640 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29640
               in
            match uu____29635 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29698 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29698
         then
           let uu____29703 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29703
         else ());
        (let uu____29710 =
           FStar_Util.record_time (fun uu____29717  -> solve env probs)  in
         match uu____29710 with
         | (sol,ms) ->
             ((let uu____29729 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29729
               then
                 let uu____29734 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29734
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29747 =
                     FStar_Util.record_time
                       (fun uu____29754  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29747 with
                    | ((),ms1) ->
                        ((let uu____29765 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29765
                          then
                            let uu____29770 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29770
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29782 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29782
                     then
                       let uu____29789 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29789
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
          ((let uu____29815 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29815
            then
              let uu____29820 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29820
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29828 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29828
             then
               let uu____29833 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29833
             else ());
            (let f2 =
               let uu____29839 =
                 let uu____29840 = FStar_Syntax_Util.unmeta f1  in
                 uu____29840.FStar_Syntax_Syntax.n  in
               match uu____29839 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29844 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3914_29845 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3914_29845.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3914_29845.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3914_29845.FStar_TypeChecker_Common.implicits)
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
            let uu____29888 =
              let uu____29889 =
                let uu____29890 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29891  ->
                       FStar_TypeChecker_Common.NonTrivial _29891)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29890;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29889  in
            FStar_All.pipe_left
              (fun _29898  -> FStar_Pervasives_Native.Some _29898)
              uu____29888
  
let with_guard_no_simp :
  'Auu____29908 .
    'Auu____29908 ->
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
            let uu____29948 =
              let uu____29949 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29950  -> FStar_TypeChecker_Common.NonTrivial _29950)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29949;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29948
  
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
          (let uu____29983 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____29983
           then
             let uu____29988 = FStar_Syntax_Print.term_to_string t1  in
             let uu____29990 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____29988
               uu____29990
           else ());
          (let uu____29995 =
             let uu____30000 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30000
              in
           match uu____29995 with
           | (prob,wl) ->
               let g =
                 let uu____30008 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30016  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30008  in
               ((let uu____30034 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30034
                 then
                   let uu____30039 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30039
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
        let uu____30060 = try_teq true env t1 t2  in
        match uu____30060 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30065 = FStar_TypeChecker_Env.get_range env  in
              let uu____30066 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30065 uu____30066);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30074 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30074
              then
                let uu____30079 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30081 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30083 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30079
                  uu____30081 uu____30083
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30109 = FStar_TypeChecker_Env.get_range env  in
          let uu____30110 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30109 uu____30110
  
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
        (let uu____30139 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30139
         then
           let uu____30144 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30146 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30144 uu____30146
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30157 =
           let uu____30164 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30164 "sub_comp"
            in
         match uu____30157 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30177 =
                 FStar_Util.record_time
                   (fun uu____30189  ->
                      let uu____30190 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30199  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30190)
                  in
               match uu____30177 with
               | (r,ms) ->
                   ((let uu____30227 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30227
                     then
                       let uu____30232 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30234 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30236 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30232 uu____30234
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30236
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
      fun uu____30274  ->
        match uu____30274 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30317 =
                 let uu____30323 =
                   let uu____30325 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30327 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30325 uu____30327
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30323)  in
               let uu____30331 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30317 uu____30331)
               in
            let equiv1 v1 v' =
              let uu____30344 =
                let uu____30349 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30350 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30349, uu____30350)  in
              match uu____30344 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30370 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30401 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30401 with
                      | FStar_Syntax_Syntax.U_unif uu____30408 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30437  ->
                                    match uu____30437 with
                                    | (u,v') ->
                                        let uu____30446 = equiv1 v1 v'  in
                                        if uu____30446
                                        then
                                          let uu____30451 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30451 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30472 -> []))
               in
            let uu____30477 =
              let wl =
                let uu___4009_30481 = empty_worklist env  in
                {
                  attempting = (uu___4009_30481.attempting);
                  wl_deferred = (uu___4009_30481.wl_deferred);
                  ctr = (uu___4009_30481.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4009_30481.smt_ok);
                  umax_heuristic_ok = (uu___4009_30481.umax_heuristic_ok);
                  tcenv = (uu___4009_30481.tcenv);
                  wl_implicits = (uu___4009_30481.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30500  ->
                      match uu____30500 with
                      | (lb,v1) ->
                          let uu____30507 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30507 with
                           | USolved wl1 -> ()
                           | uu____30510 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30521 =
              match uu____30521 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30533) -> true
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
                      uu____30557,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30559,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30570) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30578,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30587 -> false)
               in
            let uu____30593 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30610  ->
                      match uu____30610 with
                      | (u,v1) ->
                          let uu____30618 = check_ineq (u, v1)  in
                          if uu____30618
                          then true
                          else
                            ((let uu____30626 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30626
                              then
                                let uu____30631 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30633 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30631
                                  uu____30633
                              else ());
                             false)))
               in
            if uu____30593
            then ()
            else
              ((let uu____30643 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30643
                then
                  ((let uu____30649 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30649);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30661 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30661))
                else ());
               (let uu____30674 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30674))
  
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
        let fail1 uu____30747 =
          match uu____30747 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4086_30770 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4086_30770.attempting);
            wl_deferred = (uu___4086_30770.wl_deferred);
            ctr = (uu___4086_30770.ctr);
            defer_ok;
            smt_ok = (uu___4086_30770.smt_ok);
            umax_heuristic_ok = (uu___4086_30770.umax_heuristic_ok);
            tcenv = (uu___4086_30770.tcenv);
            wl_implicits = (uu___4086_30770.wl_implicits)
          }  in
        (let uu____30773 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30773
         then
           let uu____30778 = FStar_Util.string_of_bool defer_ok  in
           let uu____30780 = wl_to_string wl  in
           let uu____30782 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30778 uu____30780 uu____30782
         else ());
        (let g1 =
           let uu____30788 = solve_and_commit env wl fail1  in
           match uu____30788 with
           | FStar_Pervasives_Native.Some
               (uu____30795::uu____30796,uu____30797) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4101_30826 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4101_30826.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4101_30826.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30827 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4106_30836 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4106_30836.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4106_30836.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4106_30836.FStar_TypeChecker_Common.implicits)
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
            let uu___4118_30913 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4118_30913.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4118_30913.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4118_30913.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____30914 =
            let uu____30916 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____30916  in
          if uu____30914
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____30928 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____30929 =
                       let uu____30931 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____30931
                        in
                     FStar_Errors.diag uu____30928 uu____30929)
                  else ();
                  (let vc1 =
                     let uu____30937 =
                       let uu____30941 =
                         let uu____30943 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____30943  in
                       FStar_Pervasives_Native.Some uu____30941  in
                     FStar_Profiling.profile
                       (fun uu____30946  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____30937 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____30950 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____30951 =
                        let uu____30953 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____30953
                         in
                      FStar_Errors.diag uu____30950 uu____30951)
                   else ();
                   (let uu____30959 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____30959
                      "discharge_guard'" env vc1);
                   (let uu____30961 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____30961 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____30970 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30971 =
                                let uu____30973 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____30973
                                 in
                              FStar_Errors.diag uu____30970 uu____30971)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____30983 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____30984 =
                                let uu____30986 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____30986
                                 in
                              FStar_Errors.diag uu____30983 uu____30984)
                           else ();
                           (let vcs =
                              let uu____31000 = FStar_Options.use_tactics ()
                                 in
                              if uu____31000
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31022  ->
                                     (let uu____31024 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31024);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31068  ->
                                              match uu____31068 with
                                              | (env1,goal,opts) ->
                                                  let uu____31084 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31084, opts)))))
                              else
                                (let uu____31088 =
                                   let uu____31095 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31095)  in
                                 [uu____31088])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31128  ->
                                    match uu____31128 with
                                    | (env1,goal,opts) ->
                                        let uu____31138 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31138 with
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
                                                (let uu____31149 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31150 =
                                                   let uu____31152 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31154 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31152 uu____31154
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31149 uu____31150)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31161 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31162 =
                                                   let uu____31164 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31164
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31161 uu____31162)
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
      let uu____31182 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31182 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31191 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31191
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31205 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31205 with
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
        let uu____31235 = try_teq false env t1 t2  in
        match uu____31235 with
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
            let uu____31279 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31279 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31292 ->
                     let uu____31305 =
                       let uu____31306 = FStar_Syntax_Subst.compress r  in
                       uu____31306.FStar_Syntax_Syntax.n  in
                     (match uu____31305 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31311) ->
                          unresolved ctx_u'
                      | uu____31328 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31352 = acc  in
            match uu____31352 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31371 = hd1  in
                     (match uu____31371 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31382 = unresolved ctx_u  in
                             if uu____31382
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31406 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31406
                                     then
                                       let uu____31410 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31410
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31419 = teq_nosmt env1 t tm
                                          in
                                       match uu____31419 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4231_31429 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4231_31429.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4234_31437 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4234_31437.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4234_31437.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4234_31437.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true) (hd2 ::
                                       (FStar_List.append extra tl1))))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4238_31448 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4238_31448.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4238_31448.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4238_31448.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4238_31448.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4238_31448.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4238_31448.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4238_31448.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4238_31448.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4238_31448.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4238_31448.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4238_31448.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4238_31448.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4238_31448.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4238_31448.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4238_31448.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4238_31448.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4238_31448.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4238_31448.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4238_31448.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4238_31448.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4238_31448.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4238_31448.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4238_31448.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4238_31448.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4238_31448.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4238_31448.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4238_31448.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4238_31448.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4238_31448.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4238_31448.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4238_31448.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4238_31448.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4238_31448.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4238_31448.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4238_31448.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4238_31448.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4238_31448.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4238_31448.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4238_31448.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4238_31448.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4238_31448.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4238_31448.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4238_31448.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4238_31448.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4243_31453 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4243_31453.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4243_31453.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4243_31453.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4243_31453.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4243_31453.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4243_31453.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4243_31453.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4243_31453.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4243_31453.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4243_31453.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4243_31453.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4243_31453.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4243_31453.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4243_31453.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4243_31453.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4243_31453.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4243_31453.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4243_31453.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4243_31453.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4243_31453.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4243_31453.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4243_31453.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4243_31453.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4243_31453.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4243_31453.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4243_31453.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4243_31453.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4243_31453.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4243_31453.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4243_31453.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4243_31453.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4243_31453.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4243_31453.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4243_31453.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4243_31453.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4243_31453.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31458 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31458
                                   then
                                     let uu____31463 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31465 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31467 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31469 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31463 uu____31465 uu____31467
                                       reason uu____31469
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4249_31476  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31483 =
                                             let uu____31493 =
                                               let uu____31501 =
                                                 let uu____31503 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31505 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31507 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31503 uu____31505
                                                   uu____31507
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31501, r)
                                                in
                                             [uu____31493]  in
                                           FStar_Errors.add_errors
                                             uu____31483);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31526 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31537  ->
                                               let uu____31538 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31540 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31542 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31538 uu____31540
                                                 reason uu____31542)) env2 g1
                                         true
                                        in
                                     match uu____31526 with
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
          let uu___4261_31550 = g  in
          let uu____31551 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4261_31550.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4261_31550.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4261_31550.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31551
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
        let uu____31591 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31591 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31592 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31592
      | imp::uu____31594 ->
          let uu____31597 =
            let uu____31603 =
              let uu____31605 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31607 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31605 uu____31607
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31603)
             in
          FStar_Errors.raise_error uu____31597
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31627 = teq env t1 t2  in
        force_trivial_guard env uu____31627
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31646 = teq_nosmt env t1 t2  in
        match uu____31646 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4286_31665 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4286_31665.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4286_31665.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4286_31665.FStar_TypeChecker_Common.implicits)
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
        (let uu____31701 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31701
         then
           let uu____31706 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31708 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31706
             uu____31708
         else ());
        (let uu____31713 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31713 with
         | (prob,x,wl) ->
             let g =
               let uu____31732 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31741  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31732  in
             ((let uu____31759 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31759
               then
                 let uu____31764 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31766 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31768 =
                   let uu____31770 = FStar_Util.must g  in
                   guard_to_string env uu____31770  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31764 uu____31766 uu____31768
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
        let uu____31807 = check_subtyping env t1 t2  in
        match uu____31807 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31826 =
              let uu____31827 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31827 g  in
            FStar_Pervasives_Native.Some uu____31826
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31846 = check_subtyping env t1 t2  in
        match uu____31846 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31865 =
              let uu____31866 =
                let uu____31867 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31867]  in
              FStar_TypeChecker_Env.close_guard env uu____31866 g  in
            FStar_Pervasives_Native.Some uu____31865
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____31905 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31905
         then
           let uu____31910 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31912 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____31910
             uu____31912
         else ());
        (let uu____31917 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31917 with
         | (prob,x,wl) ->
             let g =
               let uu____31932 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____31941  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31932  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____31962 =
                      let uu____31963 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____31963]  in
                    FStar_TypeChecker_Env.close_guard env uu____31962 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32004 = subtype_nosmt env t1 t2  in
        match uu____32004 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  